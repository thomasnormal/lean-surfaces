# Canonical E fixed unpacked storage, loop-local index

This receipt runs the source-shaped fixed one-rank array through canonical E.
The retained `for (int i = 1; i < 4; i++)` loop samples variable-indexed NBA
reads from the pre-edge `MemState`; the dynamic `idx` read includes an unknown
index row.  No array unrolling or second memory representation is used.

The seven rows are compared with Icarus Verilog 13.0 and readiness-gated
Xcelium 24.03-s004.
