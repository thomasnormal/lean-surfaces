# Dynamic unpacked target wall

Slang retains `slot[idx] = x` as the parser-shaped
`AssignmentExpression:target` refusal inside an `always_comb` body.  The
canonical E memory entry stops at its earlier `always_comb` boundary, so it
does not silently lower the target or choose a memory-cell representation.

Icarus Verilog 13.0 and Xcelium 24.03-s004 execute the two source rows
(`y=00000000`, then `y=10100101`), confirming a measured E refusal.
