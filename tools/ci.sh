#!/usr/bin/env bash
# tools/ci.sh — the full local CI for lean_models. Run from anywhere; exits
# nonzero if any present component fails. Components that are not yet built
# (docs checker, notebooks, SV harness) are reported as SKIP, not silently
# omitted — so the summary always states what was and wasn't verified.
set -u
cd "$(dirname "$0")/.."

# ---------------------------------------------------------------- SAFETY
# 2026-08-23: `bash tools/ci.sh --self-test` ran the ENTIRE CI, because this
# script ignored unknown arguments — and its tool-self-test step then invoked
# ci.sh again, which invoked `lake build` with default parallelism, no nice and
# no ticket, in a clone whose cache was cold.  Twenty minutes of mathlib and
# load ~30 on Thomas's machine.
#
# Three layers, because the incident used the one path that had none:
#
#   1. THIS SCRIPT TAKES NO ARGUMENTS.  Ignoring an unknown flag is how a
#      self-test request became a full build.
#   2. AN ENVIRONMENT SENTINEL, not an argv check.  `LS_CI_SELF_TEST` is
#      inherited by EVERY descendant at any depth and through any argv, which
#      is exactly what an argv or filename guard cannot do.
#   3. THE SELF-TEST STUBS `lake`.  Under the sentinel, PATH is prefixed with a
#      no-op `lake` that refuses loudly, so a self-test CANNOT reach a real
#      build even if a future edit re-introduces a call.  A11: any lake
#      invocation needs a ticket or a stub, and a self-test has no ticket.
# An ALLOWLIST, and anything outside it still refuses.  The defect was never
# that a flag existed; it was that an unknown flag was IGNORED.
REQUIRE_BUILD=0
VERIFY_GUARDS=0
while [ "$#" -gt 0 ]; do
  case "$1" in
    --require-build) REQUIRE_BUILD=1; shift ;;
    --verify-guards) VERIFY_GUARDS=1; shift ;;
    *)
      echo "ci.sh: unknown argument (got: $*)" >&2
      echo "  Accepted: --require-build, --verify-guards.  For a tool's own" >&2
      echo "  refusal paths use 'bash tools/<tool>.sh --self-test' directly." >&2
      exit 2 ;;
  esac
done

if [ -n "${LS_CI_SELF_TEST:-}" ]; then
  echo "ci.sh: REFUSING — LS_CI_SELF_TEST is already set in this environment," >&2
  echo "  so this is a re-entry from a self-test.  CI does not run inside CI," >&2
  echo "  and a build started here would carry no ticket (A11)." >&2
  exit 2
fi

pass=(); fail=(); skip=()
step() { # step <name> <command...>
  local name="$1"; shift
  echo "=== [$name] $*"
  if "$@"; then pass+=("$name"); else fail+=("$name"); fi
}
# A FILE GIT TRACKS IS NOT OPTIONAL.  `maybe` turned ANY missing path into a
# SKIP, so deleting or renaming `tools/docs_check.py`, `harness/sv/diff_test.py`
# or `harness/spice/*.py` left CI green — 34 of 39 steps went through it.  The
# discriminator is mechanical and needs no list: if the repository tracks the
# path, its absence is a DEFECT; if it does not (a simulator binary, a
# generated artifact, an out-of-tree corpus), its absence is an environment
# fact and SKIP is honest.
maybe() { # maybe <name> <required-file> <command...>
  local name="$1" req="$2"; shift 2
  if [ -e "$req" ]; then step "$name" "$@"; return; fi
  if git ls-files --error-unmatch -- "$req" >/dev/null 2>&1; then
    echo "=== [$name] FAIL — $req is TRACKED by this repository and is missing."
    echo "    A gate file that vanished is a defect, not an absent simulator."
    fail+=("$name")
  else
    echo "=== [$name] SKIP ($req not present, and not tracked — an environment fact)"
    skip+=("$name")
  fi
}

# THE TOOLS' OWN REFUSAL PATHS.  None of them ran in CI, so a gate could rot
# silently between audits — which is how four of this lane's tools shipped with
# defects the 2026-08-23 audit had to find by reading.
selftests() {
  local t rc=0 stub
  # A no-op `lake` in front of PATH, plus the sentinel every descendant
  # inherits.  Belt (argv), suspenders (sentinel), and a stub so that even a
  # successful re-entry cannot reach a real build.
  stub="$(mktemp -d "${TMPDIR:-/tmp}/ci-selftest-stub.XXXXXX")" || return 1
  cat > "$stub/lake" <<'STUB'
#!/usr/bin/env bash
echo "lake: REFUSED — a self-test may not invoke lake (no ticket, A11)." >&2
exit 97
STUB
  chmod +x "$stub/lake"
  export LS_CI_SELF_TEST=1
  export PATH="$stub:$PATH"
  for t in tools/*.sh; do
    [ -r "$t" ] || continue
    # A CASE ARM, not the STRING.  Matching the bare string picked up `ci.sh`
    # ITSELF — which mentions --self-test in this very function — so the loop
    # re-entered CI and started an UNTICKETED `lake build`.  A tool that merely
    # talks about the flag does not accept it.
    # Both handler spellings in this tree — a `case` arm and an equality test —
    # and neither matches `ci.sh`, which only MENTIONS the flag.
    grep -qE -- '--self-test\)|= "--self-test"' "$t" || continue
    case "$t" in */ci.sh) continue ;; esac        # belt: never re-enter CI
    # A per-tool timeout, so a future tool that hangs cannot hang CI.
    if ! timeout 120 bash "$t" --self-test >/dev/null 2>&1; then
      echo "    SELF-TEST FAILED (or timed out): ${t##*/}"; rc=1
    fi
  done
  python3 tools/docs_check.py --self-test >/dev/null 2>&1 || {
    echo "    SELF-TEST FAILED: docs_check.py"; rc=1; }
  rm -rf "$stub"
  return "$rc"
}

# THE BUILD IS GATED BY HOST.  On a GitHub runner the build IS the point; on
# any other machine a bare `lake` is an unticketed Lean invocation (A11) in
# whatever clone happens to be cwd — which is how 26 recursive ci.sh instances
# each started one.  There is NO local override that reaches bare lake: a local
# caller who wants a build takes a ticket, full stop.  `--require-build` only
# turns the skip into a FAILURE, for a caller that must not proceed without it.
lake_build_step() {
  if [ "${GITHUB_ACTIONS:-}" = "true" ]; then
    step "lake-build" lake build
    return
  fi
  echo "=== [lake-build] SKIPPED on non-CI host — Lean builds go through tools/triad.sh (A11)"
  if [ "$REQUIRE_BUILD" = "1" ]; then
    echo "    --require-build was passed, so a skipped build is a FAILURE here."
    fail+=("lake-build")
  else
    skip+=("lake-build")
  fi
}

# THE SAME GATE FOR `lake env lean`.  A11 makes no exception for it — "any
# Lean process is Lean execution" — and two spice steps ran it directly.  The
# ruling was written about `lake build`; this applies its reason rather than
# its letter, and is flagged as an extension rather than smuggled in.
maybe_lean() { # maybe_lean <name> <required-file> <command...>
  local name="$1"
  if [ "${GITHUB_ACTIONS:-}" = "true" ]; then maybe "$@"; return; fi
  echo "=== [$name] SKIPPED on non-CI host — Lean builds go through tools/triad.sh (A11)"
  if [ "$REQUIRE_BUILD" = "1" ]; then fail+=("$name"); else skip+=("$name"); fi
}


# THE GUARDS, VERIFIED — placed after the definitions so it drives the REAL
# `lake_build_step` rather than a copy of it, and before any step runs.
if [ "$VERIFY_GUARDS" = "1" ]; then
  vok=0; vbad=0
  vcheck() { if [ "$2" = "$3" ]; then vok=$((vok+1)); echo "  ok   $1"; \
             else vbad=$((vbad+1)); echo "  FAIL $1: got '$2' want '$3'"; fi; }

  out="$(bash "$0" --self-test 2>&1)"; rc=$?
  vcheck "an unknown flag REFUSES, never runs CI"  "$rc" "2"
  vcheck "  ...naming what it got"                 "$(printf '%s' "$out" | grep -c -- 'got: --self-test')" "1"
  out="$(LS_CI_SELF_TEST=1 bash "$0" 2>&1)"; rc=$?
  vcheck "the sentinel REFUSES re-entry"           "$rc" "2"
  vcheck "  ...naming A11"                         "$(printf '%s' "$out" | grep -c 'A11')" "1"

  # A stub that RECORDS being called, so "no lake was invoked" is an assertion
  # rather than a hope.
  vstub="$(mktemp -d "${TMPDIR:-/tmp}/ci-vg.XXXXXX")"
  cat > "$vstub/lake" <<VSTUB
#!/usr/bin/env bash
touch "$vstub/INVOKED"
exit 97
VSTUB
  chmod +x "$vstub/lake"
  vpath="$PATH"; PATH="$vstub:$PATH"

  # CALLED DIRECTLY, output to a FILE: `$( … )` is a subshell, so the array
  # mutations the step records would be discarded — which is exactly what the
  # first cut measured, reading empty arrays as a failing gate.
  vout="$vstub/out"
  rm -f "$vstub/INVOKED"; pass=(); fail=(); skip=()
  GITHUB_ACTIONS= lake_build_step > "$vout" 2>&1
  out="$(cat "$vout")"
  vcheck "off a CI host the build is SKIPPED"      "$(printf '%s' "$out" | grep -c 'SKIPPED on non-CI host')" "1"
  vcheck "  ...naming triad.sh and A11"            "$(printf '%s' "$out" | grep -c 'tools/triad.sh (A11)')" "1"
  vcheck "  ...and NO lake was invoked"            "$( [ -e "$vstub/INVOKED" ] && echo called || echo none )" "none"
  vcheck "  ...recorded as a skip, not a pass"     "${skip[*]}" "lake-build"

  rm -f "$vstub/INVOKED"; pass=(); fail=(); skip=()
  REQUIRE_BUILD=1 GITHUB_ACTIONS= lake_build_step > "$vout" 2>&1
  vcheck "--require-build turns the skip into a FAIL" "${fail[*]}" "lake-build"
  vcheck "  ...and STILL invokes no lake"          "$( [ -e "$vstub/INVOKED" ] && echo called || echo none )" "none"

  rm -f "$vstub/INVOKED"; pass=(); fail=(); skip=()
  GITHUB_ACTIONS=true lake_build_step > "$vout" 2>&1
  vcheck "on a GitHub runner the step RUNS"        "$( [ -e "$vstub/INVOKED" ] && echo called || echo none )" "called"
  vcheck "  ...and a stubbed lake fails it"        "${fail[*]}" "lake-build"

  rm -f "$vstub/INVOKED"; pass=(); fail=(); skip=()
  GITHUB_ACTIONS= maybe_lean "probe" /etc/hosts lake env lean --run /dev/null > "$vout" 2>&1
  vcheck "lake env lean is gated the same way"    "$(grep -c 'SKIPPED on non-CI host' "$vout")" "1"
  vcheck "  ...and invokes no lake either"        "$( [ -e "$vstub/INVOKED" ] && echo called || echo none )" "none"

  PATH="$vpath"; rm -rf "$vstub"
  echo "verify-guards: $vok ok, $vbad failed"
  [ "$vbad" = "0" ] || exit 1
  exit 0
fi

step  "tool-self-tests" selftests
lake_build_step
step  "py-harness"      python3 harness/diff_test.py --no-build
# leanpy: whole PROGRAMS against CPython. Fails only on a DIVERGENCE (the
# model ran a file and disagreed) — a loud refusal is a result, and the
# completeness percentage it prints is telemetry, not a gate.
maybe "leanpy-survey"   harness/leanpy_survey.py  python3 harness/leanpy_survey.py
step  "extractor-tests" python3 extractors/python/test_extract.py
step  "leanpy-cache-tests" python3 tools/test_leanpy.py
step  "spice-extractor-tests" python3 extractors/spice/test_extract.py
maybe "spice-dram-bank-256x32-source" Examples/spice/dram_bank_256x32/generate.py \
  python3 Examples/spice/dram_bank_256x32/generate.py --check
maybe_lean "spice-dram-bank-256x32-adversarial" harness/spice/dram_bank_256x32_source_test.lean \
  lake env lean --run harness/spice/dram_bank_256x32_source_test.lean
maybe_lean "spice-dram-sense-adversarial" harness/spice/dram_sense_amp_source_test.lean \
  lake env lean --run harness/spice/dram_sense_amp_source_test.lean
maybe "circuit-equation-provenance" harness/spice/equation_provenance_test.py \
  python3 harness/spice/equation_provenance_test.py
# The Verilog-A extractor drives a pinned OpenVAF checkout (gitignored, ~785MB
# with build tree) — present on lab hosts, absent on stock runners.
maybe "verilog-a-extractor-tests" extractors/veriloga/openvaf_ast/Cargo.toml python3 extractors/veriloga/test_extract.py
maybe "docs-check"      tools/docs_check.py       python3 tools/docs_check.py
maybe "notebooks"       tools/run_notebooks.py    python3 tools/run_notebooks.py
# RV lane: differential validation of LeanModels/Rv against the pinned
# sail-riscv reference emulator (prebuilt release binary under
# tools/rv-oracle/, gitignored; absent on stock runners — the fetch URL is
# in tools/rv-oracle/README.md and in harness/rv/diff_test.py's docstring).
RV_SAIL="${RV_SAIL_SIM:-tools/rv-oracle/sail-riscv-Linux-x86_64/bin/sail_riscv_sim}"
if [ -x "$RV_SAIL" ]; then
  maybe "rv-harness" harness/rv/diff_test.py python3 harness/rv/diff_test.py --no-build
else
  echo "=== [rv-harness] SKIP (sail_riscv_sim not present at $RV_SAIL)"; skip+=("rv-harness")
fi

# SV lane: prefer Icarus when installed (generic CI and license-free local
# runs); otherwise use Xcelium on lab hosts. A mismatch is a hard failure.
if command -v iverilog >/dev/null 2>&1; then
  maybe "sv-harness" harness/sv/diff_test.py python3 harness/sv/diff_test.py --sim iverilog
elif command -v xrun >/dev/null 2>&1; then
  maybe "sv-harness" harness/sv/diff_test.py python3 harness/sv/diff_test.py --sim xrun
else
  echo "=== [sv-harness] SKIP (no simulator: neither xrun nor iverilog on PATH)"; skip+=("sv-harness")
fi
# sv-0.2 semantic tier: per-feature probes + real-core transactions (ff_one,
# popcnt, alu_div, fifo, register_file_ff). --sim auto uses every simulator
# on PATH; the case-inside probe is Xcelium-only (Icarus cannot parse it).
if command -v iverilog >/dev/null 2>&1 || command -v xrun >/dev/null 2>&1; then
  maybe "sv2-harness" harness/sv/diff_test2.py python3 harness/sv/diff_test2.py --sim auto
else
  echo "=== [sv2-harness] SKIP (no simulator: neither xrun nor iverilog on PATH)"; skip+=("sv2-harness")
fi

# SPICE lane: ngspice is the floating-point differential oracle for the exact
# rational DC solver and the analog validation oracle for switch-level gates.
if command -v ngspice >/dev/null 2>&1 || [ -x "$HOME/.local/bin/ngspice" ]; then
  maybe "spice-harness" harness/spice/diff_test.py python3 harness/spice/diff_test.py --no-build
  maybe "spice-switch-harness" harness/spice/switch_diff_test.py python3 harness/spice/switch_diff_test.py
  maybe "spice-transient-harness" harness/spice/transient_test.py python3 harness/spice/transient_test.py
  maybe "spice-rlc-transient" harness/spice/rlc_transient_test.py python3 harness/spice/rlc_transient_test.py
  maybe "spice-parser-agreement" harness/spice/parser_agreement.py python3 harness/spice/parser_agreement.py
  maybe "spice-typed-dc" harness/spice/typed_dc_test.py python3 harness/spice/typed_dc_test.py
  maybe "spice-ac-ngspice" harness/spice/ac_test.py python3 harness/spice/ac_test.py --sim ngspice
  maybe "spice-amp-ngspice" harness/spice/amp_test.py python3 harness/spice/amp_test.py
  maybe "spice-loaded-inverter-ngspice" harness/spice/loaded_inverter_transient_test.py python3 harness/spice/loaded_inverter_transient_test.py --sim ngspice
  maybe "spice-dram-1t1c-ngspice" harness/spice/dram_1t1c_transient_test.py python3 harness/spice/dram_1t1c_transient_test.py --sim ngspice
  maybe "spice-dram-bank-ngspice" harness/spice/dram_bank_2x2_transient_test.py python3 harness/spice/dram_bank_2x2_transient_test.py --sim ngspice
  maybe "spice-dram-bank-256x32-ngspice" harness/spice/dram_bank_256x32_transient_test.py python3 harness/spice/dram_bank_256x32_transient_test.py --sim ngspice
  maybe "spice-dram-sense-ngspice" harness/spice/dram_sense_amp_transient_test.py python3 harness/spice/dram_sense_amp_transient_test.py --sim ngspice
else
  echo "=== [spice-harness] SKIP (ngspice not found)"; skip+=("spice-harness")
  echo "=== [spice-switch-harness] SKIP (ngspice not found)"; skip+=("spice-switch-harness")
  echo "=== [spice-transient-harness] SKIP (ngspice not found)"; skip+=("spice-transient-harness")
  echo "=== [spice-rlc-transient] SKIP (ngspice not found)"; skip+=("spice-rlc-transient")
  echo "=== [spice-parser-agreement] SKIP (ngspice not found)"; skip+=("spice-parser-agreement")
  echo "=== [spice-typed-dc] SKIP (ngspice not found)"; skip+=("spice-typed-dc")
  echo "=== [spice-ac-ngspice] SKIP (ngspice not found)"; skip+=("spice-ac-ngspice")
  echo "=== [spice-amp-ngspice] SKIP (ngspice not found)"; skip+=("spice-amp-ngspice")
  echo "=== [spice-loaded-inverter-ngspice] SKIP (ngspice not found)"; skip+=("spice-loaded-inverter-ngspice")
  echo "=== [spice-dram-1t1c-ngspice] SKIP (ngspice not found)"; skip+=("spice-dram-1t1c-ngspice")
  echo "=== [spice-dram-bank-ngspice] SKIP (ngspice not found)"; skip+=("spice-dram-bank-ngspice")
  echo "=== [spice-dram-bank-256x32-ngspice] SKIP (ngspice not found)"; skip+=("spice-dram-bank-256x32-ngspice")
  echo "=== [spice-dram-sense-ngspice] SKIP (ngspice not found)"; skip+=("spice-dram-sense-ngspice")
fi

# Spectre is proprietary and unavailable on stock GitHub runners. Lab hosts
# run it as an independent second oracle when both the binary and a license are
# available. An installed but unlicensed binary is infrastructure absence, not
# evidence that a circuit disagrees with Spectre.
spectre_steps=(
  "spectre-harness"
  "spice-ac-spectre"
  "spice-amp-spectre"
  "verilog-a-spectre"
  "spice-loaded-inverter-spectre"
  "spice-dram-1t1c-spectre"
  "spice-dram-bank-spectre"
  "spice-dram-bank-256x32-spectre"
  "spice-dram-sense-spectre"
)
skip_spectre_steps() {
  local reason="$1" name
  for name in "${spectre_steps[@]}"; do
    echo "=== [$name] SKIP ($reason)"
    skip+=("$name")
  done
}

if command -v spectre >/dev/null 2>&1 || \
    [ -x "${SPECTRE_BIN:-/opt/cadence/installs/SPECTRE231/bin/spectre}" ]; then
  if ! command -v spectre >/dev/null 2>&1; then
    export PATH="$(dirname "${SPECTRE_BIN:-/opt/cadence/installs/SPECTRE231/bin/spectre}"):$PATH"
  fi
  python3 harness/spice/spectre_probe.py
  spectre_probe_status=$?
  if [ "$spectre_probe_status" -eq 0 ]; then
    pass+=("spectre-probe")
    maybe "spectre-harness" harness/spice/spectre_test.py python3 harness/spice/spectre_test.py
    maybe "spice-ac-spectre" harness/spice/ac_test.py python3 harness/spice/ac_test.py --sim spectre
    maybe "spice-amp-spectre" harness/spice/amp_test.py python3 harness/spice/amp_test.py --sim spectre
    maybe "verilog-a-spectre" harness/veriloga/spectre_test.py python3 harness/veriloga/spectre_test.py
    maybe "spice-loaded-inverter-spectre" harness/spice/loaded_inverter_transient_test.py python3 harness/spice/loaded_inverter_transient_test.py --sim spectre
    maybe "spice-dram-1t1c-spectre" harness/spice/dram_1t1c_transient_test.py python3 harness/spice/dram_1t1c_transient_test.py --sim spectre
    maybe "spice-dram-bank-spectre" harness/spice/dram_bank_2x2_transient_test.py python3 harness/spice/dram_bank_2x2_transient_test.py --sim spectre
    maybe "spice-dram-bank-256x32-spectre" harness/spice/dram_bank_256x32_transient_test.py python3 harness/spice/dram_bank_256x32_transient_test.py --sim spectre --full
    maybe "spice-dram-sense-spectre" harness/spice/dram_sense_amp_transient_test.py python3 harness/spice/dram_sense_amp_transient_test.py --sim spectre
  elif [ "$spectre_probe_status" -eq 77 ]; then
    skip_spectre_steps "Spectre license unavailable"
  else
    fail+=("spectre-probe")
    skip_spectre_steps "Spectre readiness probe failed"
  fi
else
  skip_spectre_steps "spectre not found"
fi

echo
echo "==================== CI SUMMARY ===================="
echo "PASS: ${pass[*]:-none}"
echo "SKIP: ${skip[*]:-none}"
echo "FAIL: ${fail[*]:-none}"
[ ${#fail[@]} -eq 0 ]
