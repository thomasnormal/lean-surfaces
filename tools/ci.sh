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
# The Verilog-A extractor drives a pinned OpenVAF checkout (gitignored, ~785MB
# with build tree) — present on lab hosts, absent on stock runners.
maybe "verilog-a-extractor-tests" extractors/veriloga/openvaf_ast/Cargo.toml python3 extractors/veriloga/test_extract.py
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
# rational DC solver and the analog validation oracle for switch-level gates.
if command -v ngspice >/dev/null 2>&1 || [ -x "$HOME/.local/bin/ngspice" ]; then
  maybe "spice-harness" harness/spice/diff_test.py python3 harness/spice/diff_test.py --no-build
  maybe "spice-switch-harness" harness/spice/switch_diff_test.py python3 harness/spice/switch_diff_test.py
  maybe "spice-transient-harness" harness/spice/transient_test.py python3 harness/spice/transient_test.py
  maybe "spice-rlc-transient" harness/spice/rlc_transient_test.py python3 harness/spice/rlc_transient_test.py
  maybe "spice-parser-agreement" harness/spice/parser_agreement.py python3 harness/spice/parser_agreement.py
  maybe "spice-typed-dc" harness/spice/typed_dc_test.py python3 harness/spice/typed_dc_test.py
  maybe "spice-ac-ngspice" harness/spice/ac_test.py python3 harness/spice/ac_test.py --sim ngspice
  maybe "spice-loaded-inverter-ngspice" harness/spice/loaded_inverter_transient_test.py python3 harness/spice/loaded_inverter_transient_test.py --sim ngspice
  maybe "spice-dram-1t1c-ngspice" harness/spice/dram_1t1c_transient_test.py python3 harness/spice/dram_1t1c_transient_test.py --sim ngspice
else
  echo "=== [spice-harness] SKIP (ngspice not found)"; skip+=("spice-harness")
  echo "=== [spice-switch-harness] SKIP (ngspice not found)"; skip+=("spice-switch-harness")
  echo "=== [spice-transient-harness] SKIP (ngspice not found)"; skip+=("spice-transient-harness")
  echo "=== [spice-rlc-transient] SKIP (ngspice not found)"; skip+=("spice-rlc-transient")
  echo "=== [spice-parser-agreement] SKIP (ngspice not found)"; skip+=("spice-parser-agreement")
  echo "=== [spice-typed-dc] SKIP (ngspice not found)"; skip+=("spice-typed-dc")
  echo "=== [spice-ac-ngspice] SKIP (ngspice not found)"; skip+=("spice-ac-ngspice")
  echo "=== [spice-loaded-inverter-ngspice] SKIP (ngspice not found)"; skip+=("spice-loaded-inverter-ngspice")
  echo "=== [spice-dram-1t1c-ngspice] SKIP (ngspice not found)"; skip+=("spice-dram-1t1c-ngspice")
fi

# Spectre is proprietary and unavailable on stock GitHub runners. Lab hosts
# run it as an independent second oracle when the licensed binary is present.
if command -v spectre >/dev/null 2>&1; then
  maybe "spectre-harness" harness/spice/spectre_test.py python3 harness/spice/spectre_test.py
  maybe "spice-ac-spectre" harness/spice/ac_test.py python3 harness/spice/ac_test.py --sim spectre
  maybe "verilog-a-spectre" harness/veriloga/spectre_test.py python3 harness/veriloga/spectre_test.py
  maybe "spice-loaded-inverter-spectre" harness/spice/loaded_inverter_transient_test.py python3 harness/spice/loaded_inverter_transient_test.py --sim spectre
  maybe "spice-dram-1t1c-spectre" harness/spice/dram_1t1c_transient_test.py python3 harness/spice/dram_1t1c_transient_test.py --sim spectre
else
  echo "=== [spectre-harness] SKIP (spectre not found)"; skip+=("spectre-harness")
  echo "=== [spice-ac-spectre] SKIP (spectre not found)"; skip+=("spice-ac-spectre")
  echo "=== [verilog-a-spectre] SKIP (spectre not found)"; skip+=("verilog-a-spectre")
  echo "=== [spice-loaded-inverter-spectre] SKIP (spectre not found)"; skip+=("spice-loaded-inverter-spectre")
  echo "=== [spice-dram-1t1c-spectre] SKIP (spectre not found)"; skip+=("spice-dram-1t1c-spectre")
fi

echo
echo "==================== CI SUMMARY ===================="
echo "PASS: ${pass[*]:-none}"
echo "SKIP: ${skip[*]:-none}"
echo "FAIL: ${fail[*]:-none}"
[ ${#fail[@]} -eq 0 ]
