# Canonical-E generate expansion over a memory

This clean-room fixture uses one source-shaped one-rank memory. A parameter
`GenerateIf` selects a nested `GenerateFor`; each generated `always_ff` keeps
its `PProcess`/`PStmt` node and writes a native `MemState` cell. The canonical
E route substitutes only the concrete genvar expression. It does not lower the
process or create scalar cell declarations.

The Lean receipt covers both the selected generate-for (`N=2`) and the
fallback generate-if (`N=1`). The rows are checked against Icarus Verilog
13.0 and Xcelium 24.03-s004 when the simulator readiness gate answers.

Regenerate the envelope from the repository root with:

```sh
python3 extractors/sv/extract.py --top generate_memory_canonical_e \
  --retain-loops --retain-proc-rewrites \
  -o Examples/system-verilog/sem2/generate_memory_canonical_e/generate_memory_canonical_e.sv.json \
  Examples/system-verilog/sem2/generate_memory_canonical_e/generate_memory_canonical_e.sv
```
