# Context-sized associative-array `exists`

IEEE 1800-2023 §7.9.3 returns a one-bit presence result from
`associative_array.exists(index)`. Equality and case-equality operands are
context-sized to the larger operand, so the self-check tier zero-extends the
finite presence bit when it is compared with a 32-bit literal. Dynamic keys,
aliases, and aggregate histories remain loud.
