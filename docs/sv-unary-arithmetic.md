# Integral unary arithmetic

IEEE 1800-2023 §11.4.3 Table 11-6 defines unary `+` and `-`; the
following arithmetic rule requires an all-x result if any operand bit is
x or z. Unary plus preserves an entirely known operand. Erasing `+` would
therefore be incorrect for a partially unknown four-state operand.

`UnaryOp.pos` and `LVec.pos` preserve this distinction. The extractor emits
`Unary` with `op: "+"` in both schemas. The M0 and self-check evaluators,
both symbolic compilers, and their nested arithmetic-operand paths call the
same value rule. Context sizing happens before the operation. Integer-only
elaboration still treats known unary plus as identity.

This repair introduces no scheduler rule. Nonintegral types and unsupported
expression/conversion shapes keep their existing named refusals.

## Oracle

The `unary-plus-arithmetic` expectation group in
`Examples/system-verilog/unary_plus/arithmetic.sv` is derived from §11.4.3
and confirmed by the source observation named beside that fixture. The
source digest binds the fixture before its trailing provenance comment was
added; executable statements are identical. No values are rescaled or
projected. The eleven checks cover partial x/z, all-z, known four-bit input,
a scalar z, signed extension, unknown extension, known/unknown 65-bit input,
concatenation, bitwise masking, and division. Every expected bit pattern has
the width explicitly written in the assertion. Any failed check prints a
named FAIL line, so the expected complete output is exactly `PASS`.

The existing `unary_plus_directed` differential case additionally drives the
real continuous assignments with four input patterns. The proof module
certifies its expression against the extracted assignment and proves known
identity and unknown collapse for arbitrary input vectors. Separate concrete
checks exercise both symbolic arithmetic-operand paths.
