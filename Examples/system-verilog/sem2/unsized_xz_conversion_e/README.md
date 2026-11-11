# Unsized x/z conversion in E memory execution

This clean-room fixture keeps the parser's `ConversionExpression:unsized-xz`
node inside the ternary `a ? 'hz1 : 'b0` and retains a source-shaped unpacked
memory read beside it.  `MemEDesign` evaluates the node through the existing
parameter expression path: IEEE 1800-2023 §5.7.1 keeps the low payload bits on
truncation and extends the payload's most-significant `z` bit when the
parameterized destination is wider.  The source marker is not lowered.

The Lean guard runs the E memory profile at `N=40` and `N=8`, checking the
parser payload, both widths, x-condition merging, and the x-valued memory
read.  `check.py` compares the same rows against Icarus and, when the refsim
readiness gate answers, Xcelium.
