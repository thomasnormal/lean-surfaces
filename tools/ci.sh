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
maybe() { # maybe <name> <required-file> <command...>
  local name="$1" req="$2"; shift 2
  if [ -e "$req" ]; then step "$name" "$@"; else
    echo "=== [$name] SKIP ($req not present)"; skip+=("$name"); fi
}

step  "lake-build"      lake build
step  "py-harness"      python3 harness/diff_test.py --no-build
step  "extractor-tests" python3 extractors/python/test_extract.py
step  "spice-extractor-tests" python3 extractors/spice/test_extract.py
maybe "docs-check"      tools/docs_check.py       python3 tools/docs_check.py
maybe "notebooks"       tools/run_notebooks.py    python3 tools/run_notebooks.py
# SV lane: prefer Icarus when installed (generic CI and license-free local
# runs); otherwise use Xcelium on lab hosts. A mismatch is a hard failure.
if command -v iverilog >/dev/null 2>&1; then
  maybe "sv-harness" harness/sv/diff_test.py python3 harness/sv/diff_test.py --sim iverilog
elif command -v xrun >/dev/null 2>&1; then
  maybe "sv-harness" harness/sv/diff_test.py python3 harness/sv/diff_test.py --sim xrun
else
  echo "=== [sv-harness] SKIP (no simulator: neither xrun nor iverilog on PATH)"; skip+=("sv-harness")
fi

# SPICE lane: ngspice is the floating-point differential oracle for the exact
# rational DC solver.
if command -v ngspice >/dev/null 2>&1 || [ -x "$HOME/.local/bin/ngspice" ]; then
  maybe "spice-harness" harness/spice/diff_test.py python3 harness/spice/diff_test.py --no-build
else
  echo "=== [spice-harness] SKIP (ngspice not found)"; skip+=("spice-harness")
fi

echo
echo "==================== CI SUMMARY ===================="
echo "PASS: ${pass[*]:-none}"
echo "SKIP: ${skip[*]:-none}"
echo "FAIL: ${fail[*]:-none}"
[ ${#fail[@]} -eq 0 ]
