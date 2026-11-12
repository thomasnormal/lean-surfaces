# Unsized x/z conversion in canonical E

This clean-room fixture keeps the parser's source-shaped
`ConversionExpression:unsized-xz` node in a parameterized continuous
assignment.  Canonical E evaluates its 32-bit, MSB-first payload at the
concrete destination width under IEEE 1800-2023 §5.7.1: truncation keeps the
low bits and widening repeats the payload's most-significant x/z bit.  No
lowering or default-point literal is introduced.

The Lean receipt checks widths 40 and 8 and executes the four assignments;
`check.py` compares the same row against Icarus Verilog 13.0 and, through the
simulator readiness gate, Xcelium 24.03-s004.
