# Canonical-E casez and casex in a memory edge process

This clean-room fixture keeps a parameterized one-rank unpacked memory and
parser-native `case`, `casez`, and `casex` statements in one `always_ff` body.
The edge route uses IEEE 1800-2023 §12.5 first-match selection and the existing
`caseHit` matcher, so wildcard bits remain four-state source semantics.  The
memory declaration and array selects stay source-shaped; no cell expansion or
case lowering is performed.

The Lean receipt runs the initial row and one rising-edge row.  The source
testbench drives exact, x, and z selectors across six differential rows.
Icarus Verilog 13.0 and
readiness-gated Xcelium 24.03-s004 are the pinned simulators.

Run:

```text
python3 Examples/system-verilog/sem2/memory_edge_casez_casex_canonical_e/check.py
```
