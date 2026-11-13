# Canonical-E case in an edge memory process

This clean-room fixture keeps a one-rank unpacked memory and a parser-native
`case` inside an `always_ff` edge body.  The edge executor evaluates the
selector at issue time, queues the selected nonblocking memory or scalar
assignment, and commits the native memory queue under IEEE 1800-2023 §§10.4.2
and 12.5.  It does not lower the case or expand the memory into cells.

The Lean receipt runs two bounded rows (the initial state and a rising edge
selecting `mem[0]`), which keeps kernel reduction practical.  The source
testbench runs six rows and additionally covers the `mem[1]` and `default`
arms.  Icarus Verilog 13.0 and readiness-gated Xcelium 24.03-s004 match all
six source rows through `check.py`.

Run:

```text
python3 Examples/system-verilog/sem2/memory_edge_case_canonical_e/check.py
```
