# Unsized x/z conversion inside a ternary

This clean-room fixture keeps the parser's `ConversionExpression:unsized-xz`
node as a branch of `a ? 'hz1 : 'b0` and also has a source-shaped dynamic
unpacked-memory read `mem[a]` so the memory route is exercised.  At a concrete
parameter point,
`instExpr2` applies IEEE 1800-2023 §5.7.1 to the marker's canonical 32-bit
payload: it keeps the low bits on truncation and extends with the payload's
most-significant `z` bit on widening.  The symbolic marker is never rewritten
or lowered before a context width is available.

The route remains loud when the marker has no destination width or an invalid
payload.  Other conversion kinds and unsupported memory expressions retain
their existing boundaries.
