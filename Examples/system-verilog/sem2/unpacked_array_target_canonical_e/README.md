# Dynamic unpacked target

Slang retains `slot[idx] = x` and `slot[idx]` as parser-shaped `ArraySel`
nodes. Canonical E executes the `always_comb` body against one native
`MemState`; a known index writes one cell, while an x/z index is a no-op for a
write and reads as all-x (IEEE 1800-2023 §§7.4.6 and 11.5.1).

The receipt covers the time-zero x state, known 0/1 indices, x/z data, and x/z
indices. Icarus Verilog 13.0 and Xcelium 24.03-s004 agree with all nine rows.
