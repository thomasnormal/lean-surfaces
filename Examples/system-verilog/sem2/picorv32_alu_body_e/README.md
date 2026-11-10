# PicoRV32 TWO_CYCLE_ALU body in E

This clean-room fixture retains the six blocking assignments from PicoRV32's
`TWO_CYCLE_ALU` `always @*` body.  The parser-shaped process remains an
`alwaysImplicit` node, and the frozen process boundary still refuses it; the
proof enters the retained body directly through E's existing `execBody`.

The lexical context contains every input and output port, including the
`reg_op2[4:0]` part-select metadata.  The seven rows cover startup, known
addition/subtraction, signed and logical shifts, x/z operand propagation, and
the separate `instr_srai` control.  `check.py` regenerates the retained
envelope and compares the kernel-computed rows with Icarus and Xcelium.
