# MemE parameter-sized unpacked storage

This clean-room fixture keeps `logic [W-1:0] s [P]` source-shaped. The retained
`for (int i = 1; i < P; i++)` writes variable-indexed NBA cells and the
run-time `s[idx]` read is executed by the existing `MemEDesign`/`MemEState`
route. It is not unrolled and does not add a second memory representation.

The receipt covers `(W,P)=(4,3)` and `(8,5)`, including an all-x index, against
Icarus Verilog 13.0 and Xcelium 24.03-s004.
