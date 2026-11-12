# MemE fixed unpacked memory, run-time loop index

This clean-room fixture keeps a fixed one-rank unpacked memory source-shaped.
The procedural `for (int i = 1; i < 4; i++)` remains a retained `PStmt.forLoop`,
its variable index selects are retained `ArraySel` nodes, and the NBA queue
samples all `s[i-1]` values before one commit.  The continuous `s[3]` and
run-time `s[idx]` reads remain source-shaped too.  No memory is unrolled and
no second memory representation is introduced.

`check.py` compares seven rows with Icarus Verilog 13.0 and with Xcelium
24.03-s004 when the readiness gate admits it.
