#!/usr/bin/env bash
# tools/ci.sh — the full local CI for lean_models. Run from anywhere; exits
# nonzero if any present component fails. Components that are not yet built
# (docs checker, notebooks, SV harness) are reported as SKIP, not silently
# omitted — so the summary always states what was and wasn't verified.
set -u
cd "$(dirname "$0")/.."

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
  local t rc=0
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
  return "$rc"
}

step  "tool-self-tests" selftests
step  "lake-build"      lake build
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
maybe "spice-dram-bank-256x32-adversarial" harness/spice/dram_bank_256x32_source_test.lean \
  lake env lean --run harness/spice/dram_bank_256x32_source_test.lean
maybe "spice-dram-sense-adversarial" harness/spice/dram_sense_amp_source_test.lean \
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
