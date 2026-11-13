# Canonical E parameterized child memory

This source-shaped receipt elaborates a parent and one parameterized child.
The child’s `logic [W-1:0] s [P]` remains one canonical `MemState`; input and
output port connections become source-shaped assignments under IEEE
1800-2023 §23.3.3. One startup row matches Icarus Verilog 13.0 and
readiness-gated Xcelium 24.03-s004. Later persistent-write rows are retained
as a performance boundary until the kernel-cheap store item; no result is
claimed for them here.
