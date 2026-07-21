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
maybe "docs-check"      tools/docs_check.py       python3 tools/docs_check.py
maybe "notebooks"       tools/run_notebooks.py    python3 tools/run_notebooks.py
# SV lane: needs Xcelium (xrun) — present on this host, absent on generic CI.
if command -v xrun >/dev/null 2>&1; then
  maybe "sv-harness"    harness/sv/diff_test.py   python3 harness/sv/diff_test.py
else
  echo "=== [sv-harness] SKIP (xrun not on PATH)"; skip+=("sv-harness")
fi

echo
echo "==================== CI SUMMARY ===================="
echo "PASS: ${pass[*]:-none}"
echo "SKIP: ${skip[*]:-none}"
echo "FAIL: ${fail[*]:-none}"
[ ${#fail[@]} -eq 0 ]
