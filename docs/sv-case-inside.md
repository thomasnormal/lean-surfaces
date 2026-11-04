# Case statements with membership labels

IEEE 1800-2023 §12.5.4 compares the case subject with each label using
`inside` (§11.4.13). Scalar labels use asymmetric wildcard equality: X/Z
bits in the label are ignored; unknown subject bits are significant at cared
positions. Colon ranges use inclusive lower/upper comparisons. A label
matches only when the result is definite one; zero and X advance the search.

The legacy/self-check extractor reuses the pure membership helpers and the
ordinary first-match case chain. Scalar labels lower to `==?`, ranges to
`>= && <=` with common signedness, and supported fixed-array labels to their
flattened scalar elements in source order. A fixed integral array cell may be
narrower than the propagated subject; it is widened at the case comparison
using the case-context signedness (sign extension for signed cells, zero
extension otherwise). A cell wider than the subject cannot be truncated. The
frontend's whole-case width and sign conversions precede comparison. The first
matching body runs once; default is the final fallback regardless of its source
position. Exhaustion without default does nothing.

Subject and label operands must belong to the admitted pure integral fragment.
The bound source is checked before folding, so calls or increments cannot
vanish into an admitted constant. Repeating pure reads during search cannot
observe another value before selection. A delayed selected body retains only
its own continuation; changed subjects or endpoints cannot restart selection.
Later visits read the current operands. No evaluator, storage or scheduler
rule changes.

Qualifiers with diagnostic obligations, tolerance ranges, nonintegral or
unsupported storage, default-only cases, dollar endpoints, dynamic or nested
arrays, and cells wider than the subject remain loud. Narrow fixed integral
cells use the case-context conversion above; no unrelated conversion is
guessed.
The ordinary `inside` expression keeps its existing dollar and array-widening
rules. The existing symbolic `Case` path retains its own structural vocabulary
and compiler boundaries.

The authored fixtures check all 256 two-bit four-state subject/item pairs,
signed/mixed/65-bit sizing, dynamic masks and ranges, reversed/ambiguous
ranges, common-width arrays/slices, first/default/no-match, nesting and delayed
arm retention with live changed operands. Three kernel theorems bind to exact
compiled source subtrees: the scalar equality bridge, skipping an ambiguous
item before a definite match, and inclusive signed range evaluation. A separate
array-widening source checks signed and unsigned narrow cells in a complete
self-check transcript; over-wide and effectful variants retain the conversion
seam as refusals.
