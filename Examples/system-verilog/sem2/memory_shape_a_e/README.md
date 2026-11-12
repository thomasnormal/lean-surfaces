# Canonical E parameterized unpacked memory, source-shaped loop

This clean-room fixture keeps one parameterized unpacked memory and its
procedural `for` loop as retained `PStmt` nodes. Canonical E evaluates the
loop at runtime for `(W,P)=(4,3)` and `(8,5)`, issues all cell NBAs from the
pre-edge state, commits them once, and then settles the continuous drivers.
The run-time `idx` row is all-x and therefore reads all-x. No memory is
unrolled and no second memory representation is introduced.

`check.py` compares 12 rows with Icarus Verilog 13.0 and with Xcelium
24.03-s004 when the readiness gate admits it.
