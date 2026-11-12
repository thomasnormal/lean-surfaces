# Parametric unsized x/z literals in canonical E

This clean-room fixture keeps unsized based x/z literals source-shaped in a
parameterized module.  Canonical E applies IEEE 1800-2023 §5.7.1 at each
concrete width: low bits survive truncation and the literal's most-significant
x/z bit is repeated on widening.  The rows cover equal, narrower, and wider
contexts at `N = 8` and `N = 40`.

The Lean receipt checks the parser markers and values.  `check.py` compares the
same two rows with Icarus Verilog 13.0 and, through the readiness gate, Xcelium
24.03-s004.
