# E memory edge loops

This clean-room fixture exercises a source-shaped canonical `for` loop over a
parameter-sized unpacked memory in an active-low reset edge body. The ordinary
E route retains the loop as a `PStmt.forLoop`; it derives the finite trip schema
from the header, issues one cell NBA per trip, and commits the updates before
the continuous `mem[0]` driver settles. The route uses the single native
`CoreMemDesign`/`MemState` store, does not unroll the source AST or use a
second memory interpreter, and keeps non-canonical loop headers, nested loops,
and non-NBA loop bodies loud.

The source and testbench are checked against Icarus Verilog 13.0 and the
readiness-gated Xcelium row set by `check.py`.
