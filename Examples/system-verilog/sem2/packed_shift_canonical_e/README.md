# Packed-register shift through canonical E

This parameterized shift register has no unpacked storage.  Its packed slice
RHS (`t[N-2:0]`) now falls through the canonical scalar expression path
instead of the old memory-only `ArraySel` refusal.

The receipt covers N=4 and N=8, including the all-x startup state.  Eight rows
match Icarus Verilog 13.0 and Xcelium 24.03-s004.
