# Generated fixed-array index wall

The parser retains the generate-for source and refuses the element select
whose index is a genvar at the symbolic default point:
`ElementSelect:default-point-index: slot[i] = x`.

Icarus Verilog 13.0 and Xcelium 24.03-s004 execute the two source rows
(`y=00000000`, then `y=10100101`), so this is a measured E refusal rather than
a simulator mismatch.
