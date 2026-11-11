# E memory edge loops

This clean-room fixture exercises a source-shaped canonical `for` loop over a
parameter-sized unpacked memory in an active-low reset edge body. The loop is
retained as a `PStmt.forLoop`; E derives its finite trip schema from the header,
issues one cell NBA per trip, and commits the updates before the continuous
`mem[0]` driver settles. The profile does not unroll the source AST and does not
use semantic fuel. Non-canonical loop headers, nested loops, and non-NBA loop
bodies remain loud.

The source and testbench are checked against Icarus Verilog 13.0 and the
readiness-gated Xcelium row set by `check.py`.
