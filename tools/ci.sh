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
  # `lean` JOINS `lake` ON THE NAME ROUTE.  Both are on PATH via elan, and a
  # stub covering one of them is a guard with a spelling in it.
  for b in lake lean; do
    cat > "$stub/$b" <<STUB
#!/usr/bin/env bash
echo "$b: REFUSED — a self-test may not invoke $b (no ticket, A11)." >&2
exit 97
STUB
    chmod +x "$stub/$b"
  done
  # AND THE OTHER ROUTE: WITHHOLD THE BUILD PRODUCTS (2026-08-26, qol-80).
  # A stub on PATH stops Lean reached BY NAME.  It does not stop Lean reached
  # BY ABSOLUTE PATH, and this repo's own runner is reached that way:
  # `tools/leanpy` runs REPO_ROOT/.lake/build/bin/leanmodels-run directly and
  # falls back to `lake` only when that file is ABSENT.  On a COLD clone the
  # stub catches the fallback and looks sufficient; on a WARM clone — every
  # working lane's — the binary is there and the stub is stepped around.  That
  # is the exact route the A11 breach of 2026-08-23 took.
  #
  # So the children run inside a symlink view of this tree with `.lake`
  # WITHHELD, which turns the absolute-path route back into the fallback the
  # stub can see.  A guard on the name covers one of the two routes; only
  # withholding the products covers the other.
  view="$(mktemp -d "${TMPDIR:-/tmp}/ci-selftest-view.XXXXXX")" || return 1
  for e in $(ls -A .); do
    [ "$e" = ".lake" ] && continue
    ln -s "$PWD/$e" "$view/$e" 2>/dev/null || true
  done
  # DELIBERATELY NOT PINNING GIT_DIR/GIT_WORK_TREE, which is the opposite of
  # what triad.sh's attested gates do, and the asymmetry is measured rather
  # than assumed.  These children `git init` their OWN fixture repos, and an
  # exported GIT_DIR would hijack every one of them; triad's gates instead
  # INSPECT the clone, where an unpinned git inside a view of symlinks calls
  # every tracked file a typechange.  Measured: the tool self-tests are 452
  # ok, 0 failed run from inside the view with no pin.
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
    if ! ( cd "$view" && timeout 120 bash "$t" --self-test ) >/dev/null 2>&1; then
      echo "    SELF-TEST FAILED (or timed out): ${t##*/}"; rc=1
    fi
  done
  ( cd "$view" && python3 tools/docs_check.py --self-test ) >/dev/null 2>&1 || {
    echo "    SELF-TEST FAILED: docs_check.py"; rc=1; }
  # The comment-form gate's own regression set, run where the other tools'
  # are: a fixture nobody runs is not a fixture.
  ( cd "$view" && python3 harness/lean_comment_forms.py --self-test ) >/dev/null 2>&1 || {
    echo "    SELF-TEST FAILED: lean_comment_forms.py"; rc=1; }
  # THE HARNESS'S OWN ROWS, not any tier's corpus.  envelope_fresh is
  # LANE-ADDED per the floor law (the corpora are per-tier), so CI gates the
  # TOOL -- including its refusal path -- while adoption stays each lane's.
  ( cd "$view" && python3 harness/envelope_fresh.py --self-test ) >/dev/null 2>&1 || {
    echo "    SELF-TEST FAILED: envelope_fresh.py"; rc=1; }
  rm -rf "$stub" "$view"
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


# IS THE MARKDOWN STRUCTURALLY INTACT?  Master shipped conflict markers TWICE
# (47544f1 committed them into docs/backlog/qol.md; a1bb01e appended around
# them rather than resolving them), and nothing noticed: no content was lost,
# `docs_check` gates marked code blocks, `backlog-index.sh` gates index
# freshness, and `## ` headings parse fine on either side of a marker.  Nothing
# was pointed at the question this asks (§5.4b).  Both were mine.
#
# THE ONE FALSE POSITIVE IT CAN HAVE, named rather than discovered: a Markdown
# SETEXT underline of exactly seven `=` is legitimate and would trip this.  The
# tree has none — measured — and this repository writes `##`, so the fix if it
# ever fires that way is the heading, not the gate.
conflict_markers() {            # [dir] -> 1 when the TRACKED tree carries any
  local d="${1:-.}" hits
  hits="$(git -C "$d" grep -nE '^(<<<<<<<|>>>>>>>|=======$)' -- . 2>/dev/null || true)"
  [ -n "$hits" ] || return 0
  echo "    CONFLICT MARKERS in the tracked tree:"
  printf '%s\n' "$hits" | head -10 | sed 's/^/      /'
  echo "    A merge was committed unresolved.  Resolve and re-commit."
  return 1
}

# EVERY VALUE-TAKING FLAG, PROBED.  `tools/triad.sh --gates` written with no
# value SPUN FOREVER, silently, burning a core: `${2:-}` accepted the missing
# value, `shift 2` then failed with one argument left, and the `while [ $# ]`
# loop re-entered on the same argument.  No output, no lock taken, nothing to
# distinguish it from waiting in the build queue — it cost the Go lane 31
# minutes across two runs.  Eleven of this lane's tools had the identical arm.
#
# DISCOVERY, NOT A LIST.  The arms are found by READING the tools, so a new
# tool or a new flag is covered without anyone remembering that this gate
# exists — a list here would have to be maintained by the same attention that
# wrote the unguarded arm in the first place.
#
# The two assertions are the two failure modes, and neither is about wording:
# the probe must TERMINATE (not 124 — that is the spin) and must NOT SUCCEED
# (not 0 — that is the near-miss, where the run continues on a DEFAULT scope
# and reports green against less than the caller asked for).
argv_guards() { # [dir] -> 1 if any value-taking flag tolerates a missing value
  local dir="${1:-tools}" stub f fl out rc n=0 bad=0 named=0
  stub="$(mktemp -d "${TMPDIR:-/tmp}/ci-argv.XXXXXX")" || return 1
  cat > "$stub/lake" <<'STUB'
#!/usr/bin/env bash
echo "lake: REFUSED — an argv probe may not invoke lake (no ticket, A11)." >&2
exit 97
STUB
  chmod +x "$stub/lake"
  for f in "$dir"/*.sh; do
    [ -r "$f" ] || continue
    # READ THE WHOLE ARM, not the first line of it.  A `grep` for
    # `--flag).*shift 2` on ONE line missed `sites.sh --channel`, whose arm
    # spans two lines because its value is appended with a newline — the same
    # under-read that had `laws.sh --gate-set` anchored at column 0 and
    # reporting 16 gates where the file declares 44.  An arm runs to its `;;`.
    for fl in $(awk '
          # A FIXTURE IS NOT A TOOL.  Without this cut the probe discovered
          # `--flag` from the two fixture scripts heredoc-ed into THIS file
          # and then probed `ci.sh --flag`, which is not one of its arms.
          /VERIFY_GUARDS" = "1"/                { fixture = 1 }
          fixture && /verify-guards: \$vok ok/  { fixture = 0; next }
          fixture                               { next }
          /^[ \t]*--[a-z-]+\)/ { flag = $0
                                 sub(/^[ \t]*/, "", flag); sub(/\).*/, "", flag)
                                 buf = ""; in_arm = 1 }
          in_arm            { buf = buf " " $0 }
          in_arm && /;;/    { if (buf ~ /shift 2/) print flag; in_arm = 0 }
        ' "$f" | sort -u); do
      n=$((n + 1))
      # Bounded, because the defect under test is an INFINITE LOOP: an
      # unguarded tool would hang this gate instead of failing it.
      out="$(LS_CI_SELF_TEST=1 PATH="$stub:$PATH" timeout 10 bash "$f" "$fl" 2>&1)"
      rc=$?
      case "$rc" in
        124) echo "    SPINS: ${f##*/} $fl — a value flag written last never returns"; bad=$((bad+1)) ;;
        0)   echo "    ACCEPTS A MISSING VALUE: ${f##*/} $fl — it continued on a default"; bad=$((bad+1)) ;;
        *)   printf '%s' "$out" | grep -q 'needs a value' && named=$((named+1)) ;;
      esac
    done
  done
  rm -rf "$stub"
  echo "    $n value-taking flags probed, $named refused by name, $bad tolerant"
  [ "$bad" = "0" ]
}

# THE SV ROUND-TRIP GATE, WHICH WAS ORPHANED.  `laws.sh --gate-set` enumerated
# the declared gate sets and found `.sv` as a kind with 21 committed envelopes
# and ZERO mentions of harness/sv_round_trip.py in this file: the SV lane's own
# gate was never in CI.  It is host-safe — it re-runs extractors/sv/extract.py
# over Examples/system-verilog/**/*.sv.json inside a scratch mirror and compares
# bytes; no simulator, no network, no Lean — and it takes no argument, reading
# the envelope root from its own location.  So it is a full step.
#
# THE INTERPRETER IS PART OF THE GATE.  The extractor imports pyslang, which
# .github/workflows/ci.yml installs under python3.12 (falling back to python3)
# and which tools/lean_magic.py names for the same reason.  Measured before
# wiring: on a dev host without it, all 18 live envelopes come back
# `REFUSE extractor-failed: ModuleNotFoundError: No module named 'pyslang'` —
# a red reporting an ABSENT PACKAGE as though it were envelope drift, which is
# the one distinction this gate exists to make.  So the interpreter is CHOSEN
# BY CAPABILITY (which python can actually import pyslang?), never by name.
sv_python() { # -> prints an interpreter that can import pyslang; 1 if none can
  local py
  for py in python3.12 python3; do
    command -v "$py" >/dev/null 2>&1 || continue
    "$py" -c "import pyslang" >/dev/null 2>&1 || continue
    printf '%s\n' "$py"; return 0
  done
  return 1
}
sv_round_trip_step() {
  local py
  if py="$(sv_python)"; then
    step "sv-round-trip" "$py" harness/sv_round_trip.py
    return
  fi
  # pyslang is NOT tracked by this repository, so its absence is an environment
  # fact and SKIP is honest — the same discriminator `maybe` applies to an
  # absent simulator.  On a GitHub runner it is not: the workflow installs it
  # there, so a runner that cannot import it has a broken install, and skipping
  # would retire the gate exactly where it is the only reader.
  if [ "${GITHUB_ACTIONS:-}" = "true" ]; then
    echo "=== [sv-round-trip] FAIL — no python3.12/python3 can import pyslang,"
    echo "    but .github/workflows/ci.yml installs it on this runner.  A gate"
    echo "    that cannot run in CI is not a skip, it is a broken install."
    fail+=("sv-round-trip")
  else
    echo "=== [sv-round-trip] SKIP (no python3.12/python3 can import pyslang —"
    echo "    an environment fact, not envelope drift; pyslang is not tracked)"
    # UNPINNED (2026-08-26), with the workflow. extract.py stamps the FAMILY
    # ("pyslang-11"), not the version, so a point release changes no committed
    # byte -- and sv_round_trip now resolves the pinned frontend before it
    # compares, refusing by name on a wrong family instead of handing anyone
    # 18 DIVERGEs and the impression that the envelopes drifted.
    echo "    To run it here: python3.12 -m pip install 'pyslang~=11.0'"
    skip+=("sv-round-trip")
  fi
}

# FRESHNESS is a different question from ROUND-TRIP, and both are needed.
# sv_round_trip asks "does the committed envelope regenerate byte-identically";
# envelope_fresh asks "does it regenerate AT ALL from the source in this tree",
# ignoring the frontend stamp. An envelope can round-trip and still be stale
# against an edited source, which is the pipeline stage nobody re-runs.
#
# Baseline at wiring (measured 2026-08-26, pyslang 11.0.0): FRESH 18, NOT-LIVE 3.
# The three not-live are sourceless (alu_div, ff_one, popcnt) and cannot become
# fresh here. ANY STALE row is now a real finding, not harness noise.
sv_envelope_fresh_step() {
  local py
  if py="$(sv_python)"; then
    step "sv-envelope-fresh" "$py" harness/envelope_fresh.py --tier sv
    return
  fi
  # Same discriminator as sv-round-trip, for the same reason: pyslang is not
  # tracked here, so its absence is an environment fact off a runner -- and a
  # BROKEN INSTALL on one, where the workflow installs it.
  if [ "${GITHUB_ACTIONS:-}" = "true" ]; then
    echo "=== [sv-envelope-fresh] FAIL — no python3.12/python3 can import pyslang,"
    echo "    but .github/workflows/ci.yml installs it on this runner.  A gate"
    echo "    that cannot run in CI is not a skip, it is a broken install."
    fail+=("sv-envelope-fresh")
  else
    echo "=== [sv-envelope-fresh] SKIP (no python3.12/python3 can import pyslang —"
    echo "    an environment fact, not envelope staleness; pyslang is not tracked)"
    echo "    To run it here: python3.12 -m pip install 'pyslang~=11.0'"
    skip+=("sv-envelope-fresh")
  fi
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

  # ---- THE ABSOLUTE-PATH ROUTE, WHICH IS THE ONE THE A11 BREACH TOOK.
  # A WARM fake clone, because warm is the only interesting case: on a COLD
  # clone the binary is absent, the fallback fires, the stub catches it, and
  # layer 3 looks sufficient while covering only one of the two routes.
  vwarm="$vstub/warm"; mkdir -p "$vwarm/.lake/build/bin" "$vwarm/tools"
  printf '#!/bin/sh\ntouch "%s/RAN-THE-BINARY"\n' "$vstub" > "$vwarm/.lake/build/bin/leanmodels-run"
  chmod +x "$vwarm/.lake/build/bin/leanmodels-run"
  # leanpy's ACTUAL shape: root from the script's own path without resolving
  # symlinks, the built binary by ABSOLUTE PATH, `lake` only as the fallback.
  printf '%s\n' '#!/bin/sh' \
    'R="$(cd "$(dirname "$0")/.." && pwd)"' \
    'if [ -x "$R/.lake/build/bin/leanmodels-run" ]; then exec "$R/.lake/build/bin/leanmodels-run"; fi' \
    'exec lake build' > "$vwarm/tools/leanpy"
  chmod +x "$vwarm/tools/leanpy"

  # (1) THE GUARD AS IT STOOD.  The stub is on PATH and the sentinel is set,
  # and neither is consulted, because nothing here is reached by name.
  rm -f "$vstub/INVOKED" "$vstub/RAN-THE-BINARY"
  ( cd "$vwarm" && LS_CI_SELF_TEST=1 sh tools/leanpy ) >/dev/null 2>&1
  vcheck "warm clone: the stub ALONE never sees it" "$( [ -e "$vstub/INVOKED" ] && echo called || echo none )" "none"
  vcheck "  ...and Lean RAN — the breach route"     "$( [ -e "$vstub/RAN-THE-BINARY" ] && echo ran || echo no )" "ran"

  # (2) THE SAME CALL FROM A .lake-LESS VIEW.  The product is withheld, so the
  # absolute path misses, the fallback fires, and the stub that was always
  # there finally has something to catch.
  vview="$vstub/view"; mkdir -p "$vview"
  for e in $(ls -A "$vwarm"); do
    [ "$e" = ".lake" ] && continue
    ln -s "$vwarm/$e" "$vview/$e" 2>/dev/null || true
  done
  rm -f "$vstub/INVOKED" "$vstub/RAN-THE-BINARY"
  ( cd "$vview" && LS_CI_SELF_TEST=1 sh tools/leanpy ) >/dev/null 2>&1; rc=$?
  vcheck "  ...from the VIEW it never reaches Lean" "$( [ -e "$vstub/RAN-THE-BINARY" ] && echo ran || echo no )" "no"
  vcheck "  ...the stub catches the fallback"       "$( [ -e "$vstub/INVOKED" ] && echo called || echo none )" "called"
  vcheck "  ...and it dies LOUDLY, not quietly"     "$rc" "97"

  # The marker gate, both directions, against a real tracked file.
  vrepo="$vstub/repo"; mkdir -p "$vrepo"; git init -q "$vrepo" 2>/dev/null
  git -C "$vrepo" config user.email v@e; git -C "$vrepo" config user.name v
  printf '# clean\n' > "$vrepo/a.md"; git -C "$vrepo" add -A
  git -C "$vrepo" commit -qm base
  conflict_markers "$vrepo" > "$vout" 2>&1
  vcheck "a clean tree passes the marker gate"    "$?" "0"
  printf '<<<<<<< HEAD\nx\n=======\ny\n>>>>>>> other\n' > "$vrepo/a.md"
  git -C "$vrepo" add -A
  conflict_markers "$vrepo" > "$vout" 2>&1
  vcheck "a committed marker FAILS the gate"      "$?" "1"
  vcheck "  ...and names the file and line"       "$(grep -c 'a.md:1' "$vout")" "1"

  # THE ARGV GATE, BOTH DIRECTIONS, ON FIXTURES.  Run against the real tools
  # it would take minutes; run against two three-line scripts it measures the
  # same two things, and the SPIN direction can be exercised for real —
  # bounded by the gate's own timeout, which is itself the thing under test.
  va="$vstub/argv"; mkdir -p "$va"
  cat > "$va/guarded.sh" <<'GUARD'
#!/usr/bin/env bash
set -u
while [ $# -gt 0 ]; do
  case "$1" in
    --flag) [ "$#" -ge 2 ] || { echo "guarded.sh: flag $1 needs a value" >&2; exit 2; }
            V="$2"; shift 2 ;;
    *) shift ;;
  esac
done
GUARD
  cat > "$va/spinner.sh" <<'SPIN'
#!/usr/bin/env bash
set -u
while [ $# -gt 0 ]; do
  case "$1" in
    --flag) V="${2:-}"; shift 2 ;;
    *) shift ;;
  esac
done
SPIN
  chmod +x "$va/guarded.sh" "$va/spinner.sh"
  argv_guards "$va" > "$vout" 2>&1
  vcheck "the argv gate FAILS on a spinner"      "$?" "1"
  vcheck "  ...naming the tool and the flag"     "$(grep -c 'SPINS: spinner.sh --flag' "$vout")" "1"
  vcheck "  ...and it TERMINATED rather than hanging" "$(grep -c 'flags probed' "$vout")" "1"
  rm -f "$va/spinner.sh"
  argv_guards "$va" > "$vout" 2>&1
  vcheck "a guarded flag PASSES the same gate"   "$?" "0"
  vcheck "  ...counted as refused BY NAME"       "$(grep -c '1 refused by name, 0 tolerant' "$vout")" "1"
  # The discovery half: a flag nobody listed anywhere is still probed.
  vcheck "arms are DISCOVERED, not listed"       "$(grep -c '1 value-taking flags probed' "$vout")" "1"

  # THE SV GATE'S INTERPRETER CHOICE, BOTH WAYS.  Stubbed rather than probed,
  # so the rows read the same on a host that has pyslang and on one that does
  # not — the failure this guards against is a gate that reports a missing
  # package as envelope drift, and that must be reproducible either way.
  mkdir -p "$vstub/svok" "$vstub/svno"
  # `$1` is escaped: the heredoc is UNQUOTED so that $vstub expands, which
  # means every other dollar has to be spelled for the stub, not for here.
  cat > "$vstub/svok/python3.12" <<SVOK
#!/usr/bin/env bash
[ "\$1" = "-c" ] && exit 0      # this interpreter CAN import pyslang
touch "$vstub/SVRAN"            # ...and records that the harness was reached
exit 0
SVOK
  cat > "$vstub/svno/python3.12" <<SVNO
#!/usr/bin/env bash
[ "\$1" = "-c" ] && exit 1      # this interpreter CANNOT import pyslang
touch "$vstub/SVRAN"
exit 0
SVNO
  cp "$vstub/svno/python3.12" "$vstub/svno/python3"
  chmod +x "$vstub/svok/python3.12" "$vstub/svno/python3.12" "$vstub/svno/python3"

  # PATH set around the call rather than as a `VAR=v func` prefix, and the
  # command hash dropped with it: bash resolves an already-hashed `python3`
  # from the hash table, which would reach the real one past the stub.
  rm -f "$vstub/SVRAN"; pass=(); fail=(); skip=()
  PATH="$vstub/svok:$vpath"; hash -r
  sv_round_trip_step > "$vout" 2>&1
  vcheck "a python that imports pyslang RUNS the gate" "$( [ -e "$vstub/SVRAN" ] && echo ran || echo none )" "ran"
  vcheck "  ...and it is a pass, not a skip"       "${pass[*]}" "sv-round-trip"

  rm -f "$vstub/SVRAN"; pass=(); fail=(); skip=()
  PATH="$vstub/svno:$vpath"; hash -r
  GITHUB_ACTIONS= sv_round_trip_step > "$vout" 2>&1
  vcheck "no pyslang off a CI host is a named SKIP" "${skip[*]}" "sv-round-trip"
  vcheck "  ...naming the package, not drift"      "$(grep -c 'not envelope drift; pyslang' "$vout")" "1"
  vcheck "  ...and the harness never ran"          "$( [ -e "$vstub/SVRAN" ] && echo ran || echo none )" "none"

  rm -f "$vstub/SVRAN"; pass=(); fail=(); skip=()
  GITHUB_ACTIONS=true sv_round_trip_step > "$vout" 2>&1
  vcheck "no pyslang ON a runner is a FAILURE"     "${fail[*]}" "sv-round-trip"
  vcheck "  ...naming the workflow that installs it" "$(grep -c 'workflows/ci.yml installs it' "$vout")" "1"

  # A TRACKED FILE IS NOT OPTIONAL: the gate is called unconditionally, and no
  # future edit may downgrade it to a `maybe`.
  vcheck "the gate is called as a full step"       "$(grep -c '^sv_round_trip_step$' "$0")" "1"
  vcheck "  ...and never as a maybe"               "$(grep -cE '^maybe(_lean)? .*sv-round-trip' "$0")" "0"

  # THE FRESHNESS GATE GETS THE SAME COVERAGE, exercised rather than assumed:
  # it shares a helper and a discriminator with the round-trip gate, and
  # "it is the same code" is the reasoning this campaign keeps convicting.
  rm -f "$vstub/SVRAN"; pass=(); fail=(); skip=()
  PATH="$vstub/svok:$vpath"; hash -r
  sv_envelope_fresh_step > "$vout" 2>&1
  vcheck "a python that imports pyslang RUNS freshness" "$( [ -e "$vstub/SVRAN" ] && echo ran || echo none )" "ran"
  vcheck "  ...and it is a pass, not a skip"       "${pass[*]}" "sv-envelope-fresh"

  rm -f "$vstub/SVRAN"; pass=(); fail=(); skip=()
  PATH="$vstub/svno:$vpath"; hash -r
  GITHUB_ACTIONS= sv_envelope_fresh_step > "$vout" 2>&1
  vcheck "no pyslang off a CI host is a named SKIP" "${skip[*]}" "sv-envelope-fresh"
  vcheck "  ...naming staleness, not drift"        "$(grep -c 'not envelope staleness; pyslang' "$vout")" "1"
  vcheck "  ...and the harness never ran"          "$( [ -e "$vstub/SVRAN" ] && echo ran || echo none )" "none"

  rm -f "$vstub/SVRAN"; pass=(); fail=(); skip=()
  GITHUB_ACTIONS=true sv_envelope_fresh_step > "$vout" 2>&1
  vcheck "no pyslang ON a runner is a FAILURE"     "${fail[*]}" "sv-envelope-fresh"
  vcheck "freshness is called as a full step"      "$(grep -c '^sv_envelope_fresh_step$' "$0")" "1"
  vcheck "  ...and never as a maybe"               "$(grep -cE '^maybe(_lean)? .*sv-envelope-fresh' "$0")" "0"

  # THE TWO GATES WIRED 2026-08-24, both directions where a direction exists.
  vcheck "lean-comment-forms is a full step"     "$(grep -c '^step  "lean-comment-forms" python3 harness/lean_comment_forms.py$' "$0")" "1"
  vcheck "  ...and never a maybe"                "$(grep -cE '^maybe(_lean)? .*lean_comment_forms' "$0")" "0"
  vcheck "  ...called with NO arguments"         "$(grep -c 'lean_comment_forms.py$' "$0")" "1"
  vcheck "backlog-headings is a full step"       "$(grep -c '^step  "backlog-headings" backlog_headings$' "$0")" "1"
  # ANCHORED TO THE DEFINITION.  A bare count matched this block's own fixture
  # invocation too and read 2 — the fixture-is-not-enforcement trap, inside the
  # row meant to enforce.
  vcheck "  ...and renders WITHOUT writing"      "$(grep -c '^backlog_headings() { bash tools/backlog-index.sh --stdout --strict' "$0")" "1"
  # A conforming fixture passes; a malformed one FAILS.  Without the second
  # row this gate could be wired to something that can never go red.
  vbl="$vstub/bl"; mkdir -p "$vbl"
  printf '## 2026-01-01-x-1 — a conforming entry\n' > "$vbl/x.md"
  bash tools/backlog-index.sh --backlog "$vbl" --stdout --strict > /dev/null 2>&1
  vcheck "a conforming backlog PASSES --strict"  "$?" "0"
  printf '## SPEC COVERAGE — a standing header\n' >> "$vbl/x.md"
  bash tools/backlog-index.sh --backlog "$vbl" --stdout --strict > /dev/null 2>&1
  vcheck "  ...and a malformed heading FAILS it" "$?" "3"

  # FRESHNESS, ITS OWN ROWS AND ITS OWN FIXTURE: a written index is in sync, a
  # hand-edited one has DRIFTED.  Kept apart from the heading rows on purpose,
  # so a failure names which promise broke.
  # ANCHORED TO THE INVOCATION LINE.  A bare substring count matched this row
  # itself and read 2 -- the same self-matching trap as the --stdout row, and
  # the third time this session that a row counted its own text.
  # RE-ANCHORED when layer 3 gained the view (qol-80): the invocation now
  # starts with the `cd`, and the row that asserts it runs has to follow it
  # there.  Still anchored at column 0 of the INVOCATION, so it cannot match
  # this line -- the self-matching trap this row's own history records.
  vcheck "the comment-form gate's own rows run"  "$(grep -c '^  ( cd "$view" && python3 harness/lean_comment_forms.py --self-test )' "$0")" "1"
  vcheck "backlog-index-fresh is its own step"     "$(grep -c '^step  \"backlog-index-fresh\" backlog_index_fresh$' "$0")" "1"
  vcheck "  ...checking freshness, not headings"   "$(grep -c 'strict' <<< "$(grep '^backlog_index_fresh()' "$0")")" "0"
  vbi="$vstub/bi"; mkdir -p "$vbi"
  printf '## 2026-01-01-y-1 — an entry\n' > "$vbi/y.md"
  bash tools/backlog-index.sh --backlog "$vbi" --dir "$vstub" > /dev/null 2>&1
  bash tools/backlog-index.sh --backlog "$vbi" --dir "$vstub" --check > /dev/null 2>&1
  vcheck "a freshly written index is in sync"      "$?" "0"
  printf '\nhand-edited\n' >> "$vbi/INDEX.md"
  bash tools/backlog-index.sh --backlog "$vbi" --dir "$vstub" --check > /dev/null 2>&1
  vcheck "  ...and a hand-edit is DRIFT"           "$?" "1"

  PATH="$vpath"; hash -r; rm -rf "$vstub"
  echo "verify-guards: $vok ok, $vbad failed"
  [ "$vbad" = "0" ] || exit 1
  exit 0
fi

step  "conflict-markers" conflict_markers
step  "argv-guards"     argv_guards
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
sv_round_trip_step
sv_envelope_fresh_step
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
# THE ANALOG LANE'S COMMENT-FORM GATE.  A full step: the file is tracked, it
# needs no arguments (its root defaults to `.`), it runs no Lean and touches
# no network — the only `lake` in it is `".lake" not in f.parts`, an exclusion.
step  "lean-comment-forms" python3 harness/lean_comment_forms.py
# HEADING SHAPE, now that the tree is at zero malformed.  `--stdout` renders
# without WRITING, so CI never dirties the tree; the rendered index is
# discarded and only the warnings (stderr) and the exit code matter.  Scoped
# deliberately to headings: `--check` would also gate INDEX freshness, which
# is a different promise and not this step's to make.
backlog_headings() { bash tools/backlog-index.sh --stdout --strict >/dev/null; }
step  "backlog-headings" backlog_headings
# INDEX FRESHNESS, A SEPARATE PROMISE AND THEREFORE A SEPARATE STEP.  `--check`
# regenerates and diffs: docs/backlog/INDEX.md is GENERATED and committed, so a
# stale one is a file that matches no tree.  It is deliberately NOT folded into
# the step above: "the headings are well-formed" and "the generated file is
# current" fail for different reasons and get fixed by different people, and a
# step that can go red for two unrelated reasons tells its reader neither.
# stdout is dropped (the in-sync line); the DRIFT report and its diff are on
# stderr and stay visible.
backlog_index_fresh() { bash tools/backlog-index.sh --check >/dev/null; }
step  "backlog-index-fresh" backlog_index_fresh
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
