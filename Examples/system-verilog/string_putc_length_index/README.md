# `string.putc` at the string length

IEEE 1800-2023 §6.16.2 leaves a string unchanged when the `putc` index is
negative or at least the current string length. The self-check tier now admits
the source-pure `s.putc(s.len(), "X")` form by replaying the literal string
history and treating the equal-to-length index as an out-of-range no-op.
Dynamic indices, aliases, controls, timing, and non-ASCII values remain loud.
