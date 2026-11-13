# Canonical-E blocking assignments in an edge memory process

This clean-room fixture keeps a one-rank unpacked memory and a plain
`always @(posedge clk)` body.  Blocking scalar and memory assignments update
the retained state in source order; the following nonblocking assignments
sample those updates at issue time and commit afterward under IEEE 1800-2023
§10.4.2.  The body remains a parser-native `PStmt`; no lowering or cell
expansion is used.

The Lean receipt runs the initial slot and one rising edge.  The source
testbench adds a second edge to check that the result is stable across slots.
Icarus Verilog 13.0 and readiness-gated Xcelium 24.03-s004 are the pinned
simulators.

Run:

```text
python3 Examples/system-verilog/sem2/memory_edge_blocking_canonical_e/check.py
```
