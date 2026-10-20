# SV corpus coverage census — sv-tests-2 vs the M0 extractor

Axis-1/2 coverage of the M0 tier (`docs/sv-design-m0.md`, envelope schema
`sv-0.1`) measured on real code: every `.sv` file under
`<corpus>/tests/chapter-*/`
(the IEEE 1800-2023 conformance corpus, self-checking PASS/FAIL tests), run
through the `extractors/sv/extract.py` pipeline **in-process** by
`extractors/sv/census.py`.

Reproduce (from the repo root):

```
python3.12 extractors/sv/census.py --corpus /path/to/tests            # full census
python3.12 extractors/sv/census.py --corpus /path/to/tests --recheck  # determinism check
```

Machine-readable results: `harness/sv/conformance/census.json`
(per-file records + this document's aggregates). The current committed summary
is the **2026-10-20** snapshot below, measured with Python 3.9 and pyslang 11;
the dated sections retain their original measurement denominators.

The committed summary uses a portable corpus-layout placeholder, not a
host-local checkout path. Supply the actual test directory explicitly.

## Numeric enumeration methods — 2026-10-20

Pure integral `first`, `last`, `num`, `next` and `prev` calls now lower
through the bound declaration-order member table. Traversal uses exact case
equality, so named x/z members remain distinct. Unsigned two-state 32-bit
step conversion precedes modular wrapping; a nonmember returns the enum base
default even at step zero. Width, signedness and receiver storage reuse the
existing rules. Effects, string-valued `name()`, unsupported storage, invalid
frontend compilations and symbolic-mode methods remain loud. No evaluator or
scheduler changed.

The paired **22,035**-path census gains **24 clean files** without losses:
**3,162 → 3,186 clean**, **18,807 → 18,783 partial**, **66 include skips**,
zero extraction errors. Twenty-two gains match complete independent
transcripts. Two delay-bearing files remain runtime refusals, including in
the timed loader because their `$time` expressions use the time-zero-only
lowering. They are counted as extraction gains only. The authored fixture
also matches its complete independent transcript, and kernel proofs bound to
its extracted assignment establish nonmember defaults and declaration-order
succession.

## Integral formatted input — 2026-10-20

The legacy/self-check tier now admits direct blocking assignments of
`$sscanf` over pure packed input, literal formats and integral packed
outputs. The shared pure scanner supports `%b/%o/%h/%x/%d/%c/%s/%v`,
suppression, positive widths, whitespace, literals and `%%`. Input is
sampled once; successful outputs copy back left to right, later selectors
see earlier writes, unmatched destinations stay unchanged, and the return
count is assigned last. Existing packed-target rules retain neighboring
bits and two-state conversion. The timed stepper delegates the new leaf to
the same interpreter; no scheduler changes. General strings, real outputs,
other contexts/formats, excess arguments, effects and symbolic scanning
remain loud. Unknown packed input and diagnostic-bearing failures are
explicit runtime boundaries. Details: [formatted input](sv-formatted-input.md).

The paired **22,035**-path census gains **34 clean files** without losses:
**3,128 → 3,162 clean**, **18,841 → 18,807 partial**, **66 include skips**,
zero extraction errors. Thirty newly clean files execute and match complete
independent transcripts. Four remain runtime refusals: two unknown-input
diagnostics, one reduction over a selected slice, and one delay-bearing
copyback fixture. These four are extraction gains only. The authored
fixtures separately check ordered/partial copyback and integral conversion
edges, including sign/underscore field-width consumption and strength input.

## Pure logical implication — 2026-10-20

Pure integral `->` lowers to `!left || right`, preserving each operand's
self-determined width, four-state truth, one-bit unsigned results and the
frontend's associativity. Both symbolic compilers reuse the existing logical
operations. M0's logical conjunction/disjunction compilation now keeps
self-determined operands, matching the second compiler. Effects, unsupported
types, frontend errors and `<->` equivalence remain loud, including constant
contexts. No evaluator or scheduler changed.

The paired **22,035**-path census moves **3,121 → 3,128 clean** and
**18,848 → 18,841 partial**, with **66 include skips**, zero extraction errors,
7 gains and no losses. Six gains execute and match complete independent
transcripts. The seventh combines continuous assignment and delay, so the
existing runners refuse it; it is counted only as an extraction gain.
Fixture-bound symbolic proofs establish dominance rules for arbitrary source
widths. Both compiler paths match the observed 16-pair truth table at widths
1, 4 and 65; the values fixture also checks vector truth, result/arithmetic
context and associativity.

## Pure integral membership — 2026-10-20

Pure integral `inside` expressions lower to wildcard equality for scalar
items, inclusive comparisons for colon ranges, and three-valued logical
disjunction across the set. Common operand width/signedness precedes the
unsigned one-bit result. Single dollar endpoints use representation limits;
fixed one-dimensional arrays and constant slices reuse flattened cells.
Effects, tolerance syntax, nonintegral/unsupported storage, frontend errors
and symbolic-mode membership remain loud. No evaluator or scheduler changed.

The paired **22,035**-path census moves **3,083 → 3,121 clean** and
**18,886 → 18,848 partial**, with **66 include skips**, zero extraction errors,
38 gains and no losses. Every newly clean file executes and matches its
complete independent simulator transcript. Files whose names mention
tolerance ranges actually contain scalar wildcard comparisons; actual
tolerance syntax remains refused. The authored `inside` fixture covers
signed/mixed sizing, wildcard uncertainty, dollar/enum limits, reversed and
unknown ranges, arrays and nesting. Its symbolic kernel proofs check
definite-match dominance and arbitrary same-width all-wildcard membership.

## Local fixed-unpacked array declarations — 2026-10-20

One-dimensional fixed-unpacked arrays whose elements are integral scalars or
packed vectors now lower to independent vector cells. Static block-local cells
are hoisted into declaration state and keep their value across repeated block
entries; automatic cells remain local declarations and are initialized on each
entry. Declaration-specific storage names preserve distinct scopes. Pure closed
static initializers, positional/keyed/default patterns already admitted by the
cell lowering, copies, constant slices, streaming cells, and two-state
conversion reuse the existing vector operations. Effectful static initializers,
multidimensional or aggregate arrays, dynamic storage and unresolved lifetimes
remain loud.

The paired **22,035**-path census moves **3,054 → 3,083 clean** and
**18,915 → 18,886 partial**, with **66 include skips**, zero extraction errors,
29 gains and no losses. `VariableDeclStatement:2state` falls from 2,453 to
2,376. All 29 newly clean files execute through the self-check runner and
match complete independent simulator transcripts. The authored `local_arrays`
fixture exercises static persistence (`4, 5, 6`) beside automatic
reinitialization (`4, 4, 4`); its kernel proof checks both cell-level rules.
Array equality and inequality combine per-cell results with the corresponding
logical conjunction or disjunction, preserving the scalar four-state rules.

## Turn 1 inventory — 2026-10-19

A fresh extractor census over the chapter-scoped `sv-tests-2` corpus used
pyslang 11 on Linux with Python 3.9. It found **22,033** source paths:
**2,628 clean**, **19,339 partial**, **66 include skips**, and **0 extraction
errors**. The include-skipped paths are multi-file tests; no extractor crash
was observed. The adapter pass marked **4** paths unlockable (two simulation
rows). This is extractor coverage only: Lean ingestion and execution remain
separate gates.

| Chapter | Total | Clean | Partial | Include skip |
|---|---:|---:|---:|---:|
| 3 | 300 | 24 | 275 | 1 |
| 4 | 427 | 121 | 306 | 0 |
| 5 | 618 | 325 | 293 | 0 |
| 6 | 1,185 | 305 | 880 | 0 |
| 7 | 796 | 14 | 782 | 0 |
| 8 | 842 | 0 | 841 | 1 |
| 9 | 589 | 60 | 529 | 0 |
| 10 | 657 | 156 | 501 | 0 |
| 11 | 1,034 | 538 | 496 | 0 |
| 12 | 627 | 167 | 460 | 0 |
| 13 | 598 | 1 | 597 | 0 |
| 14 | 473 | 1 | 472 | 0 |
| 15 | 550 | 0 | 550 | 0 |
| 16 | 1,543 | 11 | 1,532 | 0 |
| 17 | 512 | 0 | 512 | 0 |
| 18 | 851 | 1 | 815 | 35 |
| 19 | 767 | 0 | 767 | 0 |
| 20 | 825 | 122 | 703 | 0 |
| 21 | 899 | 8 | 891 | 0 |
| 22 | 572 | 371 | 173 | 28 |
| 23 | 851 | 26 | 825 | 0 |
| 24 | 355 | 9 | 346 | 0 |
| 25 | 480 | 8 | 472 | 0 |
| 26 | 565 | 1 | 564 | 0 |
| 27 | 354 | 2 | 352 | 0 |
| 28 | 737 | 6 | 731 | 0 |
| 29 | 363 | 1 | 362 | 0 |
| 30 | 443 | 0 | 443 | 0 |
| 31 | 554 | 0 | 554 | 0 |
| 32 | 286 | 0 | 286 | 0 |
| 33 | 267 | 1 | 266 | 0 |
| 34 | 228 | 93 | 134 | 1 |
| 35 | 257 | 0 | 257 | 0 |
| 36 | 720 | 3 | 717 | 0 |
| 37 | 417 | 79 | 338 | 0 |
| 38 | 340 | 170 | 170 | 0 |
| 39 | 64 | 0 | 64 | 0 |
| 40 | 87 | 4 | 83 | 0 |
| **Total** | **22,033** | **2,628** | **19,339** | **66** |

The leading extractor refusal classes are `AssignmentExpression:target`
(4,473 files), `CallExpression` (4,225), `InstanceSymbol:Instance` (3,838),
`ExpressionStatement:CallExpression` (3,717), `VariableSymbol:2state`
(3,716), `TimedStatement:DelayControl` (2,675),
`VariableDeclStatement:2state` (2,469), `SubroutineSymbol:Subroutine` (1,640),
`NamedValueExpression:2state` (1,504), `ClassType` (1,326),
`ProceduralBlockSymbol:NoEventControl` (1,307), and `InvalidStatement` (1,302).

## Fresh paired census — 2026-10-14

The October 14 summary in `docs/sv-construct-census.json` measured
**22,008** chapter-scoped paths with pyslang 11 on Linux. The older July
measurements retained after this section are historical. The current snapshot
is the October 19 comparison below.
Both sides of the integral-variable-port comparison use the same paths:
**2,572 → 2,573 clean**, **19,370 → 19,369 partial**, **66 includes skipped**,
**0 extraction errors**, **2 gains**, **1 loss**. Four paths change their
refusal sets. Both gains are chapter-23 predefined integer port declarations.
The loss is a negative fixture with a forbidden output-net port initializer
that the old extractor silently dropped. An extractor-clean classification
is not Lean admission or live execution.

The follow-up constant-`$clog2` admission uses the same paths and changes the
current snapshot to **2,580 clean** and **19,362 partial**: seven chapter-5/20
gains, no losses, and `CallExpression` falls from 4,351 to 4,328 files.

The fixed-dimension query follow-up changes the same snapshot to **2,588
clean** and **19,354 partial**: eight total chapter-20 gains from the
`$size`/`$high`/`$left`/`$right`/`$low`/`$increment` family and no losses;
`CallExpression` falls again to 4,233 files.

The scalar dimension-count follow-up adds `$dimensions` and
`$unpacked_dimensions` for the same fixed integral declarations. The fresh
census changes the snapshot to **2,596 clean** and **19,346 partial**: eight
additional gains (one in chapter 7 and seven in chapter 20), no losses, and
`CallExpression` falls to **4,207** files.

## Fixed array dimension selection — 2026-10-19

The corpus now contains **22,030** chapter-scoped paths. Both sides of a
fresh paired run use those same paths and pyslang 11 on Python 3.9. Fixed
packed/unpacked range metadata and optional static dimension operands remove
the dimension-arity refusal from **33** files; **67** files lose every
dimension-query refusal. Metadata-only type aliases also become admissible,
without admitting runtime array/aggregate storage, while erased aliases in
rejected compilations retain a diagnostic refusal. The resulting snapshot is
**2,596 clean → 2,599 clean**, **19,368 partial → 19,365 partial**,
**66 includes skipped**, **0 extraction errors**, three gains and no losses.
Two gains are chapter-20 type-operand queries; one is a chapter-6 fixture
whose unused packed-structure alias has no runtime effect. All three new
clean fixtures execute through Lean's self-check runner and agree with
independent source observations. The **22** extra paths
relative to October 14 are all partial on both sides, not regressions.

The same family corrects `$dimensions` of a plain scalar to zero while
preserving an implicit packed dimension for predefined integers, enums and
untagged packed aggregates. Dynamic storage, tagged unions, runtime dimension
selection and effects remain loud. Metadata admission is not simulator
agreement or live execution.

## Integral wildcard equality — 2026-10-19

A fresh paired run over the same **22,030** paths, with pyslang 11 on
Python 3.12, changes **2,599 → 2,628 clean** and **19,365 → 19,336 partial**,
with **66 include skips**, **zero errors**, **29 gains** and **no losses**.
All gains are in chapter 11. Thirty files lose their wildcard comparison
refusals; one remains partial because it also uses `$time`. Two gains
require both equality and inequality, beyond the 27 files with only one
of those refusal kinds. All 29 newly clean fixtures execute through Lean;
their complete outputs are checked against independent source runs.

`==?` and `!=?` share the four-state value rule documented in
[the operator contract](sv-wildcard-equality.md), including cared-left
unknowns, signed/mixed-width operands and one-bit result sizing. The
following chapter table is the current snapshot; earlier comparisons
remain historical. An extractor-clean result alone does not establish
execution or simulator agreement.

| Chapter | Total | Clean | Partial | Include skip |
|---|---:|---:|---:|---:|
| 3 | 300 | 24 | 275 | 1 |
| 4 | 427 | 121 | 306 | 0 |
| 5 | 618 | 325 | 293 | 0 |
| 6 | 1,185 | 305 | 880 | 0 |
| 7 | 796 | 14 | 782 | 0 |
| 8 | 842 | 0 | 841 | 1 |
| 9 | 589 | 60 | 529 | 0 |
| 10 | 656 | 156 | 500 | 0 |
| 11 | 1,034 | 538 | 496 | 0 |
| 12 | 627 | 167 | 460 | 0 |
| 13 | 598 | 1 | 597 | 0 |
| 14 | 473 | 1 | 472 | 0 |
| 15 | 550 | 0 | 550 | 0 |
| 16 | 1,543 | 11 | 1,532 | 0 |
| 17 | 512 | 0 | 512 | 0 |
| 18 | 851 | 1 | 815 | 35 |
| 19 | 767 | 0 | 767 | 0 |
| 20 | 825 | 122 | 703 | 0 |
| 21 | 899 | 8 | 891 | 0 |
| 22 | 572 | 371 | 173 | 28 |
| 23 | 851 | 26 | 825 | 0 |
| 24 | 355 | 9 | 346 | 0 |
| 25 | 478 | 8 | 470 | 0 |
| 26 | 565 | 1 | 564 | 0 |
| 27 | 354 | 2 | 352 | 0 |
| 28 | 737 | 6 | 731 | 0 |
| 29 | 363 | 1 | 362 | 0 |
| 30 | 443 | 0 | 443 | 0 |
| 31 | 554 | 0 | 554 | 0 |
| 32 | 286 | 0 | 286 | 0 |
| 33 | 267 | 1 | 266 | 0 |
| 34 | 228 | 93 | 134 | 1 |
| 35 | 257 | 0 | 257 | 0 |
| 36 | 720 | 3 | 717 | 0 |
| 37 | 417 | 79 | 338 | 0 |
| 38 | 340 | 170 | 170 | 0 |
| 39 | 64 | 0 | 64 | 0 |
| 40 | 87 | 4 | 83 | 0 |
| **Total** | **22,030** | **2,628** | **19,336** | **66** |

The turn-one refusal sets counted assignment targets in 4,473 files,
expression calls in 4,225, instance hierarchy in 3,838, and two-state
declaration shapes in 3,716. The current 2026-10-19 snapshot is recorded
below; counts overlap because a file may have several walls.

## Unary arithmetic correction — 2026-10-19

A fresh 22,030-path census after retaining unary `+` as an arithmetic node
had **2,599 clean**, **19,365 partial**,
**66 include skips**, and **zero extraction errors**. This is a correction to
execution of admitted expressions: partially unknown operands now produce
all x under §11.4.3. The new source fixture covers scalar, signed, widened,
65-bit and nested arithmetic uses; extraction cleanliness alone does not
establish those runtime results. See [the operator contract](sv-unary-arithmetic.md).

## Constant fixed-unpacked element cells — 2026-10-19

The self-check extractor now lowers one-dimensional fixed-unpacked integral
array elements at constant in-range indices to independent vector cells. A
fresh chapter-scoped run over the same **22,033** paths reports **2,691 clean**
and **19,276 partial**, with **66 include skips** and **0 extraction errors**:
63 clean gains and no losses relative to the turn-one snapshot. The leading
`AssignmentExpression:target` refusal falls from **4,473 to 4,314 files**.
The remaining target class is heterogeneous; dynamic/out-of-range indices,
multidimensional and aggregate arrays, hierarchy, classes, strings and
floating values remain separate loud boundaries. The real fixture and Lean
proof are in `Examples/system-verilog/unpacked_cells`; this is an extractor
and self-check result, not a whole-corpus simulator-agreement claim.

| Chapter | Total | Clean | Partial | Include skip |
|---|---:|---:|---:|---:|
| 3 | 300 | 24 | 275 | 1 |
| 4 | 427 | 122 | 305 | 0 |
| 5 | 618 | 326 | 292 | 0 |
| 6 | 1,185 | 307 | 878 | 0 |
| 7 | 796 | 28 | 768 | 0 |
| 8 | 842 | 0 | 841 | 1 |
| 9 | 589 | 60 | 529 | 0 |
| 10 | 657 | 160 | 497 | 0 |
| 11 | 1,034 | 541 | 493 | 0 |
| 12 | 627 | 167 | 460 | 0 |
| 13 | 598 | 1 | 597 | 0 |
| 14 | 473 | 1 | 472 | 0 |
| 15 | 550 | 0 | 550 | 0 |
| 16 | 1,543 | 11 | 1,532 | 0 |
| 17 | 512 | 0 | 512 | 0 |
| 18 | 851 | 1 | 815 | 35 |
| 19 | 767 | 0 | 767 | 0 |
| 20 | 825 | 128 | 697 | 0 |
| 21 | 899 | 8 | 891 | 0 |
| 22 | 572 | 372 | 172 | 28 |
| 23 | 851 | 26 | 825 | 0 |
| 24 | 355 | 9 | 346 | 0 |
| 25 | 480 | 8 | 472 | 0 |
| 26 | 565 | 1 | 564 | 0 |
| 27 | 354 | 2 | 352 | 0 |
| 28 | 737 | 6 | 731 | 0 |
| 29 | 363 | 1 | 362 | 0 |
| 30 | 443 | 0 | 443 | 0 |
| 31 | 554 | 0 | 554 | 0 |
| 32 | 286 | 0 | 286 | 0 |
| 33 | 267 | 1 | 266 | 0 |
| 34 | 228 | 93 | 134 | 1 |
| 35 | 257 | 0 | 257 | 0 |
| 36 | 720 | 3 | 717 | 0 |
| 37 | 417 | 91 | 326 | 0 |
| 38 | 340 | 189 | 151 | 0 |
| 39 | 64 | 0 | 64 | 0 |
| 40 | 87 | 4 | 83 | 0 |
| **Total** | **22,033** | **2,691** | **19,276** | **66** |

## Whole-vector arbitrary packed ranges — 2026-10-19

The self-check extractor now admits whole-vector declarations and operations
over one-dimensional packed scalar ranges with arbitrary left/right bounds.
Selected reads and writes on noncanonical ranges remain loud because the
current evaluator still needs explicit bound mapping. The fresh run over the
same **22,033** paths reports **2,726 clean**, **19,241 partial**, **66 include
skips**, and **0 extraction errors**: 35 additional clean files with no
losses. `AssignmentExpression:target` falls from **4,314 to 4,224 files**;
`CallExpression` is now the leading refusal at **4,226**. The `packed_ranges`
fixture and proof run through the self-check surface; this is not a simulator
agreement claim for the corpus.

The chapter deltas from the preceding cell census are:

| Chapter | Clean | Partial | Include skip |
|---|---:|---:|---:|
| 6 | 310 | 875 | 0 |
| 7 | 33 | 763 | 0 |
| 10 | 165 | 492 | 0 |
| 11 | 550 | 484 | 0 |
| 20 | 140 | 685 | 0 |
| 38 | 190 | 150 | 0 |

## Time-zero `$time` queries — 2026-10-19

The self-check extractor folds zero-argument `$time` expressions to a 64-bit
zero literal with `time_zero` provenance. A fresh run over the same
**22,033** paths reports **2,789 clean**, **19,178 partial**, **66 include
skips**, and **0 extraction errors**: 63 additional clean files and no
losses. `CallExpression` falls from **4,226 to 3,565** files, while timed
processes still retain their delay/event refusals. The `time_zero` fixture and
Lean proof pass; this is not a whole-corpus simulator-agreement claim.

## Constant bit selects on arbitrary packed ranges — 2026-10-19

The self-check extractor now normalizes in-range constant bit selects on
one-dimensional noncanonical packed ranges to the existing LVec index
geometry. Dynamic/out-of-range indices and part-selects remain loud. The
fresh **22,033**-path run reports **2,795 clean**, **19,172 partial**, **66
include skips**, and **0 extraction errors**: 6 additional clean files with
no losses. `AssignmentExpression:target` falls from **4,224 to 4,223 files**.
The `packed_range_select` fixture and proof pass through Lean; this is not a
whole-corpus simulator-agreement claim.

## Positional fixed-unpacked initializers — 2026-10-19

Exact-length positional assignment patterns now populate the vector cells of
eligible one-dimensional fixed-unpacked integral declarations. Keyed/default,
wrong-length, effectful and aggregate initializers remain loud. The fresh
**22,033**-path run reports **2,798 clean**, **19,169 partial**, **66 include
skips**, and **0 extraction errors**: 3 additional clean files with no
losses. The `unpacked_init` fixture and Lean proof pass; this is not a
whole-corpus simulator-agreement claim.

## Direct packed-struct field windows — 2026-10-19

Direct fields of untagged packed structs and packed unions now lower to fixed
bit windows over their aggregate vector identifier. Nested/unpacked members,
classes, interfaces, tagged unions and nonintegral fields remain loud. The
fresh **22,033**-path run reports **2,886 clean**, **19,081 partial**, **66
include skips**, and **0 extraction errors**: 88 additional clean files with
no losses. `AssignmentExpression:target` falls **4,223 → 4,051** and
`MemberAccessExpression` falls **1,299 → 1,203**. The `packed_struct` fixture
and proof pass through Lean; this is not a whole-corpus simulator-agreement
claim.

## Whole-array positional assignment patterns — 2026-10-19

Whole assignments to eligible one-dimensional fixed-unpacked integral arrays
now admit an exact-length positional pattern. The extractor expands the
pattern into per-cell assignments over the same vector-cell state used for
constant element access and declaration initializers. Keyed/default,
wrong-length, dynamic, aggregate and destination-aliasing patterns remain
loud. A paired run over **22,029** chapter-scoped paths reports **2,889
clean**, **19,074 partial**, **66 include skips**, and **0 extraction errors**:
four clean gains and no losses on that checkout; the target wall falls by 23
files (**4,049 → 4,026**). The `unpacked_assign` fixture and Lean proof pass
through the self-check runner. This is not a whole-corpus simulator-agreement
claim.

## Assignment-target repricing — 2026-10-19

The paired target census leaves **87** files whose only recorded blocker is
`AssignmentExpression:target`, containing **117** target instances. The
remaining instances split by source shape as follows; a file may occur in more
than one row.

| residual target shape | instances | files |
|---|---:|---:|
| keyed/default/replicated or unpacked-array pattern RHS | 30 | 29 |
| dynamic element target | 21 | 17 |
| concatenated or streaming target | 16 | 15 |
| whole aggregate/array target | 18 | 13 |
| packed or unpacked part-select target | 13 | 9 |
| member target (nested packed, union or unsupported member) | 16 | 7 |
| constant element/bit target in a continuous or unsupported shape | 3 | 3 |

The next broad aggregate tier is not priced as a safe admission: dynamic and
unpacked aggregate targets require a runtime aggregate store, while the
continuous concatenation and part-select rows require continuous-assignment
scheduling. Nested/unpacked/class/interface member targets remain loud, and
the direct packed-struct window tier stays limited to untagged direct integral
fields. A future item must name one of those prerequisites and supply its
representation before lowering any wider target family.

Reproduce the table with
`python3.9 extractors/sv/target_reprice.py --corpus <corpus>/tests`; the
instrument reads the source in-process and writes no envelopes beside the
corpus.

## Bounded dynamic fixed-array cells — 2026-10-19

Pure integral dynamic accesses to one-dimensional fixed-unpacked arrays now
lower to finite conditional paths over the declaration's expanded vector
cells. Case-equality dispatch preserves x/z-index no-op writes and all-x
out-of-range reads. Dynamic/associative/queue storage, multidimensional arrays
and effectful indices remain loud. The paired **22,029**-path run reports
**2,906 clean**, **19,057 partial**, **66 include skips**, and **0 extraction
errors**: 17 clean gains and no losses; `AssignmentExpression:target` falls
**4,026 → 3,999**. The `unpacked_dynamic` fixture and proof pass through the
self-check runner. This is not a whole-corpus simulator-agreement claim.

## Equal-length fixed-array copies — 2026-10-19

Whole assignment between equal-length one-dimensional fixed-unpacked integral
arrays now pairs their already expanded cells in declaration order. Different
lengths, incompatible element widths, conditional aggregate expressions and
unsupported storage forms remain loud. The paired **22,029**-path run reports
**2,915 clean**, **19,048 partial**, **66 include skips**, and **0 extraction
errors**: nine additional clean files with no losses; the target wall falls
**3,999 → 3,978**. The `unpacked_copy` fixture and proof pass through the
self-check runner. This is not a whole-corpus simulator-agreement claim.

## Conditional fixed-array assignments — 2026-10-19

Pure one-condition ternaries over equal-length fixed-unpacked integral arrays
now lower cell by cell to existing `Ternary` values. An x condition therefore
keeps the per-bit conditional merge, while patterns, calls, unequal shapes and
unsupported aggregate storage remain loud. The paired **22,029**-path run
reports **2,918 clean**, **19,045 partial**, **66 include skips**, and **0
extraction errors**: three additional clean files with no losses; the target
wall falls **3,978 → 3,974**. The `unpacked_conditional` fixture and proof
pass through the self-check runner. This is not a whole-corpus simulator-
agreement claim.

## Constant fixed-array slice patterns — 2026-10-19

Simple in-range constant slices of eligible fixed-unpacked integral arrays now
accept exact-length positional patterns and lower to the selected cells in
source order. Dynamic/indexed/out-of-range slices and keyed/default patterns
remain loud. The paired **22,029**-path run reports **2,919 clean**, **19,044
partial**, **66 include skips**, and **0 extraction errors**: one additional
clean file with no losses; the target wall falls **3,974 → 3,972**. The
`unpacked_slice` fixture and proof pass through the self-check runner. This is
not a whole-corpus simulator-agreement claim.

## Structured and replicated fixed-array patterns — 2026-10-19

Elaborated keyed/default patterns on eligible fixed-unpacked integral arrays
now lower their per-cell elements in declaration order. Constant replicated
patterns are admitted when the repetition count exactly equals the array
length. Wrong-length, dynamic, aggregate and destination-aliasing forms remain
loud. The `unpacked_patterns` fixture and proof pass through the self-check
runner. The external `sv-tests-2` checkout was unavailable for this turn, so
the committed census snapshot is unchanged and no fresh whole-corpus gain is
claimed. This is not a whole-corpus simulator-agreement claim.

## Structured and replicated fixed-array initializers — 2026-10-19

The same elaborated structured keyed/default and exact-length constant
replicated patterns now populate eligible fixed-unpacked declaration cells.
Wrong-length, effectful and aggregate initializers remain loud. The
`unpacked_init_patterns` fixture and proof pass through the self-check runner.
The external `sv-tests-2` checkout was unavailable for this turn, so the
committed census snapshot is unchanged and no fresh whole-corpus gain is
claimed. This is not a whole-corpus simulator-agreement claim.

## Constant part selects on arbitrary packed ranges — 2026-10-19

In-range constant simple part selects on one-dimensional noncanonical packed
scalar ranges now normalize their right bound to the existing LVec offset for
both reads and writes. Dynamic, out-of-range and indexed part-selects remain
loud. The `packed_range_part_select` fixture and proof pass through the
self-check runner. The external `sv-tests-2` checkout was unavailable for this
turn, so the committed census snapshot is unchanged and no fresh whole-corpus
gain is claimed. This is not a whole-corpus simulator-agreement claim.

## Constant fixed-array slice copies — 2026-10-19

Equal-length simple constant slices of eligible fixed-unpacked integral arrays
now pair their expanded cells for copies, including a whole-array source or
destination on either side. Overlapping self-copies, dynamic/indexed and
out-of-range slices remain loud because no temporary aggregate snapshot is
introduced. The `unpacked_slice_copy` fixture and proof pass through the
self-check runner. The external `sv-tests-2` checkout was unavailable for this
turn, so the committed census snapshot is unchanged and no fresh whole-corpus
gain is claimed. This is not a whole-corpus simulator-agreement claim.

## Structured and replicated fixed-array slice patterns — 2026-10-19

Elaborated keyed/default and exact-length constant replicated patterns now
populate simple constant fixed-array slices cellwise. Dynamic, indexed,
out-of-range and mismatched forms remain loud. The `unpacked_slice_patterns`
fixture and proof pass through the self-check runner. The external
`sv-tests-2` checkout was unavailable for this turn, so the committed census
snapshot is unchanged and no fresh whole-corpus gain is claimed. This is not a
whole-corpus simulator-agreement claim.

## Conditional fixed-array slice assignments — 2026-10-19

Equal-length simple constant slices on a fixed-array destination and both
branches of a pure ternary now lower cellwise to existing `Ternary` nodes.
Overlapping source/destination names, dynamic/indexed and out-of-range slices
remain loud. The `unpacked_slice_conditional` fixture and proof pass through
the self-check runner. The external `sv-tests-2` checkout was unavailable for
this turn, so the committed census snapshot is unchanged and no fresh
whole-corpus gain is claimed. This is not a whole-corpus simulator-agreement
claim.

## Fixed-array equality and inequality — 2026-10-19

Equal-length whole fixed-unpacked arrays and simple constant slices now compare
cellwise, joining the per-cell `==` or `!=` results with logical `&&`.
Unequal shapes and unsupported aggregate types remain loud. The
`unpacked_compare` fixture and proof pass through the self-check runner. The
external `sv-tests-2` checkout was unavailable for this turn, so the committed
census snapshot is unchanged and no fresh whole-corpus gain is claimed. This
is not a whole-corpus simulator-agreement claim.

## Fixed-array case equality and inequality — 2026-10-19

Equal-length whole arrays and simple constant slices now lower `===` and `!==`
to pairwise cell case comparisons joined by logical `&&`, preserving exact
x/z matching. Unequal shapes and unsupported aggregate types remain loud. The
`unpacked_compare` fixture and proof cover both ordinary and case comparisons.
The external `sv-tests-2` checkout was unavailable for this turn, so the
committed census snapshot is unchanged and no fresh whole-corpus gain is
claimed. This is not a whole-corpus simulator-agreement claim.

## Unpacked-array concatenation into fixed cells — 2026-10-19

Exact-length unpacked-array concatenations now flatten scalar and eligible
whole-array/simple-slice operands in source order and lower them to the
existing fixed-cell assignments. Destination aliases, dynamic or aggregate
operands and mismatched lengths remain loud. The `unpacked_concat` fixture and
proof pass through the self-check runner. The fresh **22,033**-path census
reports **2,952 clean**, **19,015 partial**, **66 include skips**, and **0
extraction errors**: nine additional clean files with no losses; the
`AssignmentExpression:target` wall falls **3,939 → 3,929**. This is not a
whole-corpus simulator-agreement claim.

## Unpacked assignment-pattern LHS — 2026-10-19

An exact positional unpacked pattern on the LHS now pairs its direct scalar
targets with cells from an eligible fixed-unpacked integral RHS, preserving
source-order sampling and destination width/state conversion. Nested,
effectful, duplicate or aliased targets and aggregate or dynamic RHS forms
remain loud. The `unpacked_pattern_lhs` fixture and Lean proof pass through the
self-check runner. The focused rerun cleans the corresponding §10.9.11 target
row; the committed machine census is unchanged because generated outputs are
not committed.

## Right-streaming unpack targets — 2026-10-19

Simple right-streaming unpack targets with no slice size and direct integral
identifier leaves now reuse the existing packed `ConcatTarget` executor. The
RHS is sampled once; a wider source contributes its leading target-width bits.
Left streaming, nested/effectful streams, unpacked aggregate leaves
and a narrower source remain loud. The `streaming_unpack`
fixture and Lean proof pass through the self-check runner. The next fresh
census reports **2,960 clean**, **19,007 partial**, **66 include skips** and
**zero extraction errors**: seven clean gains with no losses; the
`AssignmentExpression:target` wall falls **3,928 → 3,920**. This is not a
simulator-agreement claim.

## Legacy streaming packed-member windows — 2026-10-20

The legacy right-streaming path now admits a constant member chain through an
untagged packed struct or union as one fixed `SelectTarget` leaf. The
`streaming_aggregate_member` fixture splits one sampled four-bit source into a
two-bit member and scalar output; nested packed-union alias leaves are pinned
by the focused extractor battery. Dynamic or effectful member indices, nested
streaming operators, left streaming and sized streams remain loud. No
aggregate runtime store or scheduler behavior was added, and the broad corpus
census was not regenerated for this focused rung.

## Whole packed values in right-streaming targets — 2026-10-20

Whole untagged packed structs/unions now lower to whole-vector streaming
leaves, including local typedef values and flattened fixed-array cells. The
`streaming_packed_value` fixture checks field order, union aliases, x/z and
leading-bit truncation against its extracted statements and a completed
simulator run. The newly admitted §11.4.14 corpus row also agrees on its full
transcript. The wider-source check corrected both extraction modes: streaming
unpack selects the source's leading bits rather than the low bits kept by an
ordinary packed resize.

A paired run over **22,035** paths reports **2,979 → 2,980 clean**,
**18,990 → 18,989 partial**, **66 include skips**, and **zero extraction
errors**: exactly one clean gain, no losses, and the
`AssignmentExpression:target` wall falls **3,942 → 3,941**. The committed
summary is regenerated from this run. The target-only repricing now leaves
**24 files / 31 instances**, with no concatenated/streaming target-only file;
the residual families still require runtime storage or driver-resolution work.
These counts establish extraction coverage only.

## Packed right-streaming sources — 2026-10-20

Pure packed integral right-streaming sources now reuse source-order `Concat`,
including optional slice sizes (ignored for `>>`). A wider destination adds
zeros at the right before destination two-state conversion. `streaming_pack`
and its symbolic theorem check the real extracted assignment;
`streaming_pack_fixed` exercises both symbolic assignment paths and process
orders. Completed simulator transcripts match both authored fixtures and all
18 newly clean corpus files. Smaller destinations, left/nested streams, `with`
selectors, unpacked
aggregate operands and symbolic parameter/generate families remain loud.

On the same **22,035** paths, **2,980 → 2,998 clean** and **18,989 → 18,971
partial**, with **66 include skips**, **zero extraction errors**, and no
clean losses. `ConversionExpression:StreamingConcat` falls **55 → 36** files;
one further partial file loses only that wall. The machine-readable summary
records this snapshot; these are extraction counts.

## Packed left-streaming sources — 2026-10-20

Packed left streams now lower through fixed selects and `Concat`: low chunks
first, original bit order inside each chunk, and no padding inside a final
short high chunk (§11.4.14.2). A wider destination receives trailing zeros
after reordering. `streaming_left` checks the extracted chunk expression with
a symbolic kernel theorem; `streaming_left_fixed` covers both symbolic process
orders. All 20 newly clean corpus files match their complete simulator output.
Nested/effectful streams, `with` selectors, unpacked aggregates, smaller
destinations and symbolic parameter/generate widths remain loud.

On the same **22,035** paths the pair reports **2,998 → 3,018 clean**,
**18,971 → 18,951 partial**, **66 include skips**, **zero extraction errors**
and no losses. `ConversionExpression:StreamingConcat` falls **36 → 16** files.
The committed summary records this extraction snapshot.

## Legacy continuous fixed-window targets — 2026-10-20

The legacy/self-check extractor now lowers constant packed bit/part selects,
fixed concatenation leaves, and direct untagged packed struct/union members on
continuous assignments to the existing `SelectTarget` windows. The focused
extractor tests cover member and vector writes, static overlap refusal, and
dynamic-index loudness. Tagged, effectful, dynamic fixed-array-cell and
unsupported net-resolution forms remain loud; a constant cell is an
ordinary flat identifier. The broad corpus census was not regenerated for this
focused rung.

## Legacy continuous nested packed-struct windows — 2026-10-20

The focused extractor battery now pins constant bit, simple part and indexed
selections through nested untagged packed-struct member chains as fixed vector
windows on continuous assignments, including flattened fixed-array aggregate
cells. Nested untagged packed unions use the same flat-vector alias windows;
dynamic and unpacked aggregate forms remain outside the tier. No broad census
or simulator-agreement claim is made for this focused boundary.

## Legacy continuous packed-union alias windows — 2026-10-20

Focused extraction now covers direct untagged packed-union members and their
constant indexed windows through the flat vector state. Alternate members
share the same static overlap guard, so conflicting continuous windows remain
loud. Nested untagged unions use the recursive window path below; tagged
unions, dynamic or effectful selections and unpacked storage stay outside this
focused rung. No broad census or simulator-agreement claim is made.

## Legacy continuous nested packed-union alias windows — 2026-10-20

Constant selections through nested untagged packed unions now accumulate fixed
outer offsets and flatten to the existing `SelectTarget` and `SelectRead`
windows. Alternate nested-union members alias one flat vector, while the
static overlap guard rejects conflicting continuous drivers before they could
imply resolution. Dynamic/effectful selections, tagged aggregates and unpacked
storage remain loud; no alias table, aggregate store or second scheduler is
introduced.

## Legacy continuous fixed-array cell windows — 2026-10-20

The legacy continuous-assignment path now has focused coverage for constant
packed bit/part and indexed selections inside flattened one-dimensional
fixed-unpacked cells. Canonical and noncanonical labels normalize to the
existing `SelectTarget`/`SelectRead` offsets, while static overlap is rejected
before it could imply driver resolution. Dynamic or effectful packed indices,
dynamic array indices, and aggregate storage remain loud. This is a focused
extractor boundary; the broad corpus census was not regenerated.

## Legacy continuous noncanonical indexed windows — 2026-10-20

Focused extraction now admits constant `+:` and `-:` selections on
noncanonical packed ranges for direct vectors, nested packed-struct members,
and flattened fixed-array cells. The indexed base is normalized to the
existing fixed-window offset and direction is retained; dynamic/effectful,
out-of-range, aggregate and unsupported net-resolution forms remain loud.
The new boundary tests are extractor-only and do not claim a broad census or
simulator agreement.

## Legacy continuous right-streaming cell windows — 2026-10-20

Simple right-streaming continuous targets now have focused coverage for direct
fixed-array cells, constant packed windows inside cells and direct packed
members of cells. The existing `ConcatTarget` split samples the RHS once;
left/sized/nested streams, dynamic or effectful leaves, aggregate storage and
overlapping windows remain loud. This focused extractor rung does not claim a
broad census or simulator agreement.

## Symbolic streaming targets over fixed cells — 2026-10-20

The symbolic `sv-0.2` procedural path now lowers simple right-streaming
assignments whose leaves are constant packed windows or constant cells of a
flattened fixed-unpacked integral array. `fixed_array_stream_target` samples a
five-bit RHS once, writes `arr[0]` and a scalar leaf in source order, and reads
the cell through the existing comb settle. Dynamic/effectful array indices,
dynamic packed bounds, left/sized/nested streams and aggregate leaves remain
loud. This semantic-only fixture does not change the legacy corpus census or
claim simulator agreement.

## Symbolic continuous streaming targets over fixed cells — 2026-10-20

Continuous right-streaming assignments now reuse the symbolic `ConcatTarget`
window path for constant packed leaves and constant flattened fixed-array cells.
`fixed_array_stream_continuous` samples a five-bit source once, writes `arr[0]`
and a scalar leaf in source order, and reads the cell through comb settle.
Dynamic/effectful leaves, left/sized/nested streams, aggregates and overlapping
windows remain loud. This semantic-only fixture does not change the legacy
corpus census or claim simulator agreement.

## Symbolic nested packed-union alias windows — 2026-10-20

Nested untagged packed-union member chains now accumulate fixed declaration
offsets and lower to `PartSel` windows over the outer vector. The focused
symbolic tests check alternate-field alias visibility and reject overlapping
constant drivers through the existing guard. Dynamic/effectful, tagged and
unpacked aggregate paths remain loud; no aggregate store, driver-resolution
rule or scheduler is added, and the legacy census is unchanged.

## Nested packed-struct field windows — 2026-10-19

Member reads and writes through a chain of untagged packed structs now flatten
the fixed declaration offsets into one `SelectRead`/`SelectTarget` window over
the outer vector. Nested unions, unpacked members, classes, interfaces and
tagged aggregates remain loud. The `packed_struct_nested` fixture and Lean
proof pass through the self-check runner. The fresh **22,033**-path census
reports **2,975 clean**, **18,992 partial**, **66 include skips** and **zero
extraction errors**: 15 clean gains with no losses; the
`AssignmentExpression:target` wall falls **3,920 → 3,909**. This is not a
simulator-agreement claim.

## Typed assignment-pattern operands in unpacked concatenations — 2026-10-19

Unpacked-array concatenations now also flatten a typed simple assignment
pattern whose fixed-array elements are pure integral values at the destination
width. Replicated, nested or mismatched pattern operands remain loud. The
focused §10.10.1 rows now extract cleanly. The fresh **22,033**-path census
reports **2,979 clean**, **18,988 partial**, **66 include skips** and **zero
extraction errors**: four clean gains with no losses; the
`AssignmentExpression:target` wall falls **3,909 → 3,904**. This is not a
simulator-agreement claim beyond the fixture.

## Nested replicated assignment patterns — 2026-10-19

Fixed-array assignment-pattern replication now repeats an inner positional
element list when the constant repetition count times that list length equals
the destination length. Wrong-length, effectful and aggregate forms remain
loud. The §5.11 nested-replication row and a focused fixture pass through the
self-check runner; the fresh census below records the paired result.

The fresh **22,033**-path census reports **2,980 clean**, **18,987 partial**,
**66 include skips** and **zero extraction errors**: one clean gain with no
losses; the `AssignmentExpression:target` wall falls **3,904 → 3,902**. This
is not a simulator-agreement claim beyond the fixture.

## Historical method

* **Walk**: 21,336 `.sv` files in `tests/chapter-3` … `chapter-40` (445
  additional `.sv` files sit directly under `tests/` outside any chapter and
  are out of scope). Metadata (`:name:`/`:tags:`/`:type:`) parsed from each
  header; 1,366 files have no `:type:` line.
* **Pipeline**: the worker calls the same functions `extract.process_file`
  calls (`SyntaxTree.fromText` → `Compilation` → `convert_design`) without
  writing `.sv.json` files into the corpus. Cross-validated on 40 random
  files against the `extract.py` CLI: identical Unsupported sets.
* **Classes**:
  * `skip_include` — the file has a real `` `include `` directive
    (multi-file test; a single-file compile would classify a partial parse,
    so these are skipped with reason). 29 files, 27 of them in chapter-22.
  * `error` — the pipeline raised, or hit the 90 s per-file alarm.
  * `clean` — envelope has **zero** `Unsupported` nodes.
  * `partial` — envelope has `Unsupported` nodes; the distinct `sv_kind`
    values are recorded per file.
* **Determinism**: `--recheck` re-runs a seed-20260721 sample of 200 files
  and compares (status, kinds, adapter blockers, unlockable) — **200/200
  identical** on this census.
* **Runtime**: full census in **3.9 s** (32 workers, 96-core host) — far
  under the 15 min target; the corpus is many small files and pyslang's
  parser is C++.

## (a) Headline counts

| class | files | share |
|---|---:|---:|
| partial | 21,278 | 99.73% |
| clean | 29 | 0.14% |
| skip_include | 29 | 0.14% |
| **EXTRACT-ERROR** | **0** | 0% |
| total | 21,336 | |

Clean by `:type:` (clean / total of that type):

| :type: | clean / total | note |
|---|---:|---|
| simulation | 5 / 18,001 | all 5 are pragma/`protect` tests; 3 have **zero modules** (vacuously clean), none prints PASS via M0 constructs |
| compile_error | 18 / 1,747 | negative tests: *illegal* SV that happens to parse into M0 vocabulary — see robustness notes |
| shell / compile_warning / (none) | 6 / 1,435 | |

The corpus-wide truth: **no self-checking simulation test is runnable at
M0**, because self-checking requires `initial` + `$display`, both outside
the tier — exactly the Adapter phase's motivation.

## (b) Construct-frequency table — THE IMPLEMENTATION PRIORITY QUEUE

Number of `partial` files whose envelope contains each `sv_kind`
(a file counts once per distinct kind), top 60, sorted descending. **This
table is the implementation priority queue for growing the tier**: each row
is "how many corpus files stop being blocked-by-this if the construct is
implemented".

> Caveat: the extractor collapses whole out-of-tier *processes* into a
> single `Unsupported` node, so `ProceduralBlockSymbol:Initial` (row 1)
> hides everything inside `initial` bodies. Section (e) re-measures the
> queue with the adapter tier treated as supported — that residual table is
> the true post-Adapter queue.

| sv_kind | files blocked |
|---|---:|
| `ProceduralBlockSymbol:Initial` | 20569 |
| `VariableSymbol:2state` | 6911 |
| `InstanceSymbol:Instance` | 3658 |
| `ConversionExpression:width` | 3231 |
| `TimedStatement:DelayControl` | 2673 |
| `SubroutineSymbol:Subroutine` | 1414 |
| `ClassType` | 1289 |
| `ProceduralBlockSymbol:NoEventControl` | 1274 |
| `PrimitiveInstanceSymbol:PrimitiveInstance` | 1016 |
| `VariableSymbol:signed` | 839 |
| `TypeAliasType:TypeAlias` | 799 |
| `PackageSymbol` | 735 |
| `VariableSymbol:type` | 709 |
| `CovergroupType:CovergroupType` | 652 |
| `CheckerSymbol` | 563 |
| `ClockingBlockSymbol:ClockingBlock` | 549 |
| `CheckerInstanceSymbol:CheckerInstance` | 534 |
| `ParameterSymbol:Parameter` | 518 |
| `ClassType:ClassType` | 503 |
| `PropertySymbol:Property` | 464 |
| `WildcardImportSymbol:WildcardImport` | 371 |
| `PrimitiveSymbol` | 371 |
| `ConfigBlockSymbol` | 271 |
| `SequenceSymbol:Sequence` | 261 |
| `GenerateBlockArraySymbol:GenerateBlockArray` | 258 |
| `GenerateBlockSymbol:GenerateBlock` | 250 |
| `TransparentMemberSymbol:TransparentMember` | 239 |
| `TypeAliasType` | 205 |
| `GenvarSymbol:Genvar` | 195 |
| `InstanceArraySymbol:InstanceArray` | 182 |
| `AssignmentExpression:target` | 180 |
| `SignalEventControl:None_` | 149 |
| `GenericClassDefSymbol` | 137 |
| `SubroutineSymbol` | 119 |
| `ExplicitImportSymbol:ExplicitImport` | 104 |
| `VariableSymbol:range` | 92 |
| `ExpressionStatement:UnaryExpression` | 90 |
| `ProceduralBlockSymbol:Final` | 83 |
| `VariableSymbol` | 76 |
| `NetSymbol:Tri` | 66 |
| `RangeSelectExpression` | 63 |
| `CallExpression` | 56 |
| `NetSymbol:Supply1` | 56 |
| `NetSymbol:WAnd` | 53 |
| `SignalEventControl:clock` | 53 |
| `NetSymbol:TriReg` | 53 |
| `NetSymbol:WOr` | 50 |
| `TransparentMemberSymbol` | 50 |
| `TimedStatement:ImplicitEventControl` | 49 |
| `SpecifyBlockSymbol:SpecifyBlock` | 49 |
| `EmptyMemberSymbol:EmptyMember` | 48 |
| `CaseStatement` | 48 |
| `NetSymbol:Supply0` | 47 |
| `PortSymbol:2state` | 42 |
| `GenericClassDefSymbol:GenericClassDef` | 39 |
| `NetSymbol:UserDefined` | 38 |
| `DefParamSymbol:DefParam` | 37 |
| `NetType` | 34 |
| `TimedStatement:EventListControl` | 33 |
| `LetDeclSymbol:LetDecl` | 33 |

## (c) Per-chapter coverage

| chapter | total | clean | partial | skip | clean % |
|---|---:|---:|---:|---:|---:|
| chapter-3 | 232 | 1 | 230 | 1 | 0.4% |
| chapter-4 | 424 | 0 | 424 | 0 | 0.0% |
| chapter-5 | 613 | 0 | 613 | 0 | 0.0% |
| chapter-6 | 1155 | 0 | 1155 | 0 | 0.0% |
| chapter-7 | 771 | 0 | 771 | 0 | 0.0% |
| chapter-8 | 805 | 0 | 805 | 0 | 0.0% |
| chapter-9 | 563 | 0 | 563 | 0 | 0.0% |
| chapter-10 | 629 | 3 | 626 | 0 | 0.5% |
| chapter-11 | 1014 | 0 | 1014 | 0 | 0.0% |
| chapter-12 | 596 | 0 | 596 | 0 | 0.0% |
| chapter-13 | 597 | 0 | 597 | 0 | 0.0% |
| chapter-14 | 464 | 0 | 464 | 0 | 0.0% |
| chapter-15 | 523 | 0 | 523 | 0 | 0.0% |
| chapter-16 | 1511 | 0 | 1511 | 0 | 0.0% |
| chapter-17 | 510 | 0 | 510 | 0 | 0.0% |
| chapter-18 | 816 | 0 | 816 | 0 | 0.0% |
| chapter-19 | 695 | 0 | 695 | 0 | 0.0% |
| chapter-20 | 782 | 0 | 782 | 0 | 0.0% |
| chapter-21 | 857 | 0 | 857 | 0 | 0.0% |
| chapter-22 | 567 | 4 | 536 | 27 | 0.7% |
| chapter-23 | 814 | 3 | 811 | 0 | 0.4% |
| chapter-24 | 347 | 4 | 343 | 0 | 1.2% |
| chapter-25 | 473 | 1 | 472 | 0 | 0.2% |
| chapter-26 | 562 | 0 | 562 | 0 | 0.0% |
| chapter-27 | 350 | 0 | 350 | 0 | 0.0% |
| chapter-28 | 721 | 0 | 721 | 0 | 0.0% |
| chapter-29 | 352 | 0 | 352 | 0 | 0.0% |
| chapter-30 | 427 | 0 | 427 | 0 | 0.0% |
| chapter-31 | 501 | 0 | 501 | 0 | 0.0% |
| chapter-32 | 286 | 0 | 286 | 0 | 0.0% |
| chapter-33 | 267 | 1 | 266 | 0 | 0.4% |
| chapter-34 | 228 | 12 | 215 | 1 | 5.3% |
| chapter-35 | 256 | 0 | 256 | 0 | 0.0% |
| chapter-36 | 720 | 0 | 720 | 0 | 0.0% |
| chapter-37 | 417 | 0 | 417 | 0 | 0.0% |
| chapter-38 | 340 | 0 | 340 | 0 | 0.0% |
| chapter-39 | 64 | 0 | 64 | 0 | 0.0% |
| chapter-40 | 87 | 0 | 87 | 0 | 0.0% |
| **total** | **21336** | **29** | **21278** | **29** | **0.14%** |

(Chapter-34 leads only because `pragma protect` envelopes elaborate to
empty/trivial designs; chapter-24's cleans are illegal-`program` negative
tests. No clean row represents a runnable self-checking test.)

## (d) M0-relevant deep-dive: chapters 4, 6, 11 — the unlockable set

**Definition (precise).** The Adapter phase's self-check tier extends M0
with exactly: `initial` blocks, `$display`/`$finish` calls, string
literals, and local variable declarations (M0-typed: unsigned 4-state
scalar or `[W-1:0]`, with M0/string initializers). A test is **unlockable**
iff it is `partial`, has ≥ 1 module, and re-walking its *elaborated AST*
with those four constructs treated as supported leaves zero blockers —
i.e. `initial` bodies are descended into (the envelope collapses them into
one `Unsupported` node, so envelope tags alone cannot decide this) and
everything inside must be M0 vocabulary (`begin/end`, `=`, `<=`, `if/else`,
M0 expressions) or the four constructs; `$display`/`$finish` arguments may
be string literals or M0 expressions; `$display` is likewise accepted
inside `always` bodies. Counts below are over `:type: simulation` tests.

| chapter | sim tests | clean | partial | **unlockable** | blocked by more |
|---|---:|---:|---:|---:|---:|
| chapter-4 | 420 | 0 | 420 | **0** | 420 |
| chapter-6 | 1011 | 0 | 1011 | **3** | 1008 |
| chapter-11 | 974 | 0 | 974 | **8** | 966 |

The 11 files are listed in `harness/sv/conformance/unlockable.txt`
(corpus-relative paths). Corpus-wide the same definition unlocks **265**
simulation tests (421 files counting non-simulation types).

**The four-construct tier is necessary but nowhere near sufficient for
these chapters.** What still blocks the rest (top residual blockers among
non-unlockable simulation tests, per chapter):

| chapter-4 | files | chapter-6 | files | chapter-11 | files |
|---|---:|---|---:|---|---:|
| `TimedStatement:DelayControl` | 346 | `AssignmentExpression:target` | 543 | `AssignmentExpression:target` | 549 |
| `ConversionExpression:width` | 202 | `VariableSymbol:2state` | 449 | `BinaryExpression:CaseEquality` | 383 |
| `VariableSymbol:2state` | 155 | `NamedValueExpression:2state` | 420 | `NamedValueExpression:2state` | 305 |
| `BinaryExpression:CaseEquality` | 143 | `BinaryExpression:LogicalAnd` | 314 | `VariableDeclStatement:2state` | 273 |
| `AssignmentExpression:target` | 140 | `VariableDeclStatement:2state` | 224 | `BinaryExpression:LogicalAnd` | 209 |
| `NamedValueExpression:2state` | 132 | `TypeAliasType:TypeAlias` | 216 | `BinaryExpression:CaseInequality` | 203 |
| `BinaryExpression:LogicalAnd` | 121 | `BinaryExpression:CaseEquality` | 215 | `VariableSymbol:2state` | 166 |
| `BinaryExpression:CaseInequality` | 69 | `CallExpression` | 198 | `ConversionExpression:width` | 119 |
| `InstanceSymbol:Instance` | 51 | `BinaryExpression:CaseInequality` | 187 | `NamedValueExpression:signed` | 101 |
| `TimedStatement:SignalEventControl` | 37 | `TimedStatement:DelayControl` | 169 | `VariableDeclStatement:signed` | 84 |

Chapter 4 (scheduling) is structurally about `#delay`/event control — its
unlockable set is empty because nearly every test *is about* timing.
Chapters 6/11 are dominated by 2-state types (`int`/`bit` locals and
module vars), `===`/`!==`, `&&`/`||`, and bit/part-select assignment
targets (`AssignmentExpression:target`).

Greedy increments — each row adds one construct to the adapter tier and
shows the cumulative unlockable count over ch. 4/6/11 simulation tests
(base 11):

| + construct | cumulative unlockable (ch 4/6/11) |
|---|---:|
| `BinaryExpression:CaseEquality` (`===`) | 71 |
| `BinaryExpression:CaseInequality` (`!==`) | 126 |
| `TimedStatement:DelayControl` (`#d`) | 167 |
| `ConversionExpression:width` (implicit resize) | 227 |
| `InstanceSymbol:Instance` (hierarchy) | 300 |
| `BinaryExpression:LogicalAnd` (`&&`) | 359 |
| `RangeSelectExpression` (`[a:b]`) | 378 |
| `ConversionExpression:StreamingConcat` | 397 |
| `BinaryExpression:LogicalOr` (`\|\|`) | 415 |
| `PrimitiveInstanceSymbol:PrimitiveInstance` | 431 |

`===`/`!==` is the single cheapest high-yield add (the Lean value core
`LeanModels/Sv/Basic.lean` already has the case-equality ops — this is
extractor-vocabulary + envelope work only).

## (e) The post-Adapter priority queue (corpus-wide, simulation tests)

Residual blocker frequency over all non-unlockable `partial` simulation
tests with the adapter tier treated as supported — the *true* queue once
initial bodies are visible (top 30; `Call:<name>` = a call other than
`$display`/`$finish`):

| adapter-residual blocker | sim files blocked |
|---|---:|
| `AssignmentExpression:target` | 7498 |
| `TimedStatement:DelayControl` | 7343 |
| `NamedValueExpression:2state` | 6357 |
| `VariableSymbol:2state` | 6158 |
| `ConversionExpression:width` | 4746 |
| `BinaryExpression:LogicalAnd` | 4688 |
| `VariableDeclStatement:2state` | 3792 |
| `InstanceSymbol:Instance` | 3219 |
| `BinaryExpression:CaseEquality` | 3215 |
| `BinaryExpression:CaseInequality` | 2325 |
| `CallExpression` | 2235 |
| `RepeatLoopStatement` | 1214 |
| `SubroutineSymbol:Subroutine` | 1175 |
| `ClassType` | 1086 |
| `ProceduralBlockSymbol:NoEventControl` | 1068 |
| `TimedStatement:SignalEventControl` | 1031 |
| `PrimitiveInstanceSymbol:PrimitiveInstance` | 921 |
| `NewClassExpression` | 857 |
| `MemberAccessExpression` | 830 |
| `InvalidStatement` | 797 |
| `VariableSymbol:signed` | 763 |
| `ElementSelectExpression` | 747 |
| `HierarchicalValueExpression` | 745 |
| `TypeAliasType:TypeAlias` | 696 |
| `NamedValueExpression:signed` | 640 |
| `VariableSymbol:type` | 634 |
| `PackageSymbol` | 597 |
| `CovergroupType:CovergroupType` | 558 |
| `ClockingBlockSymbol:ClockingBlock` | 450 |
| `BinaryExpression:LogicalOr` | 443 |

The corpus-wide greedy sequence (simulation, base 265):
`InvalidStatement`→578, `+InstanceSymbol:Instance`→887,
`+TimedStatement:DelayControl`→1014, `+BinaryExpression:CaseEquality`→1378,
`+ConversionExpression:width`→1909, `+BinaryExpression:CaseInequality`→2399,
`+PrimitiveInstance`→2842, `+PrimitiveSymbol`→3119. Headline: the
four-construct adapter tier + {`===`, `!==`, `#delay`, width-changing
implicit conversions, bit/part-select targets, 2-state locals} is the
shortest path to a four-digit conformance suite.

## Symbolic continuous concatenation targets — 2026-10-19

The fresh paired extractor census remains **2,980 clean / 18,987 partial / 66
include skips / 0 errors**; `AssignmentExpression:target` remains **3,902**
files because this item changes only the symbolic `sv-0.2` surface. The
target-only repricing is **18 files / 27 instances**, all continuous-assignment
shapes. The new semantic slice admits the direct nested-concatenation subset
through existing comb-settle windows and therefore makes no whole-corpus
clean-count claim. `sem2/concat_assign` exercises source-order flattening,
single-RHS sampling, and x-state propagation through the symbolic runner.

The follow-on `selected_assign` fixture exercises two disjoint constant
part-select continuous drivers through the same symbolic executor. It is a
semantic-tier acceptance case only: the legacy target-only census remains
unchanged because these corpus rows require the scheduler-facing continuous
assignment surface.

The `bit_select_assign` fixture adds the one-bit form: two disjoint constant
bit-select drivers, one fed by a selected source bit and one by a scalar input.
Its trace checks live updates, undriven x bits, and x propagation. This is
also a semantic-tier acceptance case only; the target-only census remains
unchanged for the same scheduler-facing reason.

The `packed_member_assign` fixture then checks direct members of an untagged
packed struct. Fixed field offsets become the same packed windows for writes
and reads, including an x-bearing source. This remains a semantic-tier
acceptance case; the legacy target-only census is unchanged.

The `packed_member_typedef` fixture covers the equivalent typedef spelling.
The alias is discarded as compile-time metadata while the canonical packed
width and member offsets remain in the emitted vector windows.

The `packed_member_nested` fixture checks a two-level untagged packed-struct
chain. Its inner fields flatten to the outer vector's fixed windows, with the
same four-state trace and no new aggregate store.

The `packed_union_assign` fixture checks direct untagged packed-union aliasing:
one field is driven, while a same-width alternate field and the whole union
read the same vector bits. Tagged unions remain outside this slice; nested
untagged union chains use the recursive alias-window slice below.

The `packed_union_typedef` fixture covers the same aliasing through an
untagged packed-union typedef; the alias is erased while the vector width is
retained.

The `indexed_part_assign` fixture covers literal indexed part-selects. Both
`+:` and `-:` forms normalize to the same fixed windows, while dynamic bases
remain loud; this is a semantic-tier fixture with no legacy census change.

The `noncanonical_part_assign` fixture covers simple constant parts on a
`[10:3]` packed range. Source and destination labels normalize to LVec offsets
before the existing window executor runs; this remains a symbolic-only result.

The `noncanonical_bit_assign` fixture applies the same normalization to
literal bit-selects and keeps dynamic noncanonical indices loud.

The symbolic extractor also rejects statically overlapping constant drivers
across separate assignments. The focused regression keeps the first driver
and makes the conflicting process loud; no driver-resolution rule is inferred.

The `packed_member_concat` fixture checks a sampled RHS split across two
disjoint packed-struct member windows, with the member outputs read back from
the same vector.

The `packed_member_subrange` fixture checks a constant `[1:0]` slice inside a
packed member, flattened to the corresponding outer-vector window with x
propagation. Dynamic nested selections remain loud.

The `packed_member_bit` fixture checks a literal bit-select inside a packed
member. Its one-bit write is flattened to the corresponding outer-vector
window and read back through the member, including x propagation; dynamic
nested selections remain loud.

The `packed_union_subrange` fixture applies the same constant-window lowering
to a direct member of an untagged packed union and reads the written bits
through its alternate field. The one-vector alias and x propagation are
preserved; tagged, nested and dynamic union paths remain loud.

The `packed_union_bit` fixture checks the one-bit form through the same union
alias. A literal bit write is visible through the alternate field with x
propagation; tagged, nested and dynamic union paths remain loud.

The `packed_member_indexed` fixture checks literal `+:` and `-:` slices inside
a direct packed-struct member. Both directions flatten to disjoint outer
windows and preserve x propagation; dynamic, parameter-dependent,
noncanonical and effectful nested selections remain loud.

The `packed_union_indexed` fixture checks both literal indexed directions on a
direct untagged packed-union member and reads the shared windows through the
alternate field. Alias visibility and x propagation are preserved; tagged,
nested, dynamic, parameter-dependent, noncanonical and effectful union paths
remain loud.

The `noncanonical_member_subrange` fixture checks a simple `[10:9]` slice of a
`[10:7]` packed-struct member. Declaration labels flatten to the corresponding
outer window with x propagation; direction-mismatched, dynamic, indexed and
effectful nested selections remain loud.

The `noncanonical_union_subrange` fixture applies the same `[10:9]` to `[10:7]`
label mapping to a direct packed-union member and reads the shared window
through its alternate field. Alias visibility and x propagation are preserved;
direction-mismatched, dynamic, indexed and effectful union paths remain loud.

The `noncanonical_member_bit` fixture checks a literal `[10]` select of a
`[10:7]` packed-struct member. The selected declaration label maps to the
outer one-bit window with x propagation; dynamic and effectful nested indices
remain loud.

The `noncanonical_union_bit` fixture applies the same `[10]` mapping to a
direct `[10:7]` packed-union member and reads the bit through its alternate
field. Alias visibility and x propagation are preserved; dynamic and effectful
union indices remain loud.

The `typedef_member_indexed` fixture checks a `+:` slice through an untagged
packed-struct typedef. The alias disappears while the field's fixed outer
window and x propagation remain; tagged, unresolved, dynamic and effectful
alias paths remain loud.

The `typedef_union_indexed` fixture checks the same `+:` slice through an
untagged packed-union typedef and reads it through the alternate field. Alias
visibility and x propagation remain; tagged, unresolved, dynamic and effectful
alias paths remain loud.

The `noncanonical_typedef_subrange` fixture checks a `[10:9]` slice through a
`[10:7]` packed-struct typedef. Alias erasure preserves declaration-label
offsets and x propagation; direction-mismatched, dynamic, indexed and
effectful alias paths remain loud.

The `noncanonical_typedef_union_subrange` fixture applies the same `[10:9]`
mapping through an untagged packed-union typedef and reads the shared bits
through its alternate field. Alias visibility and x propagation remain;
direction-mismatched, dynamic, indexed and effectful union aliases remain
loud.

The `noncanonical_typedef_bit` fixture checks a literal `[10]` select through a
`[10:7]` packed-struct typedef. Alias erasure preserves the one-bit outer
offset and x propagation; dynamic and effectful alias indices remain loud.

The `noncanonical_typedef_union_bit` fixture applies the same `[10]` mapping
through an untagged packed-union typedef and reads the bit through its alternate
field. Alias visibility and x propagation remain; dynamic and effectful union
aliases remain loud.

The `nested_member_indexed` fixture checks a `+:` slice of a member inside a
two-level untagged packed-struct chain. Recursive fixed offsets flatten to the
outer window with x propagation; nested unions, direction mismatches, dynamic
and effectful paths remain loud.

The `nested_member_bit` fixture checks a literal bit of the same nested member
chain. Recursive offsets flatten to the one-bit outer window with x
propagation; nested unions, dynamic and effectful paths remain loud.

The `nested_noncanonical_subrange` fixture checks `[10:9]` of a `[10:7]` final
member in the same nested chain. Recursive and local declaration offsets flatten
to the outer window with x propagation; direction mismatches, dynamic, indexed
and effectful paths remain loud.

The `nested_noncanonical_bit` fixture checks `[10]` of that `[10:7]` final
member. Recursive and local offsets flatten to the one-bit outer window with x
propagation; dynamic and effectful paths remain loud.

The `nested_member_concat` fixture checks one sampled RHS split across two
disjoint slices of nested members. Recursive windows receive the high and low
RHS pieces in source order with x propagation; dynamic, aliased, duplicate,
overlapping and effectful leaves remain loud.

The `typedef_nested_concat` fixture checks the same nested concatenation through
an untagged packed-struct typedef. Alias erasure preserves recursive windows,
source-order splitting and x propagation; tagged, unresolved, dynamic,
duplicate, overlapping and effectful alias leaves remain loud.

The `nested_noncanonical_concat` fixture checks one sampled RHS split across
`[10:9]` slices of two `[10:7]` final members in a nested chain. Recursive and
local declaration offsets preserve source-order splitting and x propagation;
direction-mismatched, dynamic, duplicate, overlapping and effectful leaves
remain loud.

The `fixed_array_element` fixture checks the symbolic one-dimensional
fixed-unpacked cell boundary. A no-initializer `logic [3:0] arr [0:1]`
declaration becomes the two vector cells `arr[0]` and `arr[1]`; a constant
element assignment and nested bit read use the existing symbolic identifiers,
while dynamic array indices remain loud. This is a semantic-only fixture: the
legacy corpus census and its target-only counts are unchanged, and no aggregate
storage or dynamic array executor is introduced.

The `typedef_fixed_array_element` fixture exercises the same boundary through
an untagged plain packed integral typedef. Alias metadata is erased and the
canonical `[3:0]` element range is retained on each emitted cell, so the
symbolic loader accepts the envelope and the constant write/read trace remains
`0`, `1`, `x`. Signed, 2-state, unresolved and aggregate aliases remain loud;
the legacy corpus census is unchanged.

The `enum_fixed_array_element` fixture carries the same flat-cell storage
through an ordinary four-state enum element type. Each cell keeps its `TypeRef`
metadata, while the constant enum-member write and cell read produce the
member's two-bit vector. Signed, 2-state and aggregate enum storage remain
loud; the legacy corpus census is unchanged.

The `packed_aggregate_array_member` fixture applies the same cell lowering to
untagged packed struct and union elements. Constant member writes and reads
reuse `PartSel` windows over `sa[0]` and `ua[0]`, including the union's alias
view. Tagged, nested-unpacked and dynamic aggregate paths remain loud; the
legacy corpus census is unchanged.

The `fixed_array_initializer` fixture exercises the declaration-time form of
the same flat storage. A pure positional assignment pattern populates `arr[0]`
and `arr[1]` before the continuous reads, producing `first=0001` and
`second=xxxx`; keyed/default and exact replicated patterns are covered by the
extractor tests. Wrong-length, effectful, nested and packed-aggregate
initializers remain loud, and the legacy corpus census is unchanged.

The `fixed_array_concat_target` fixture makes a cell one leaf of a symbolic
`ConcatTarget`. Source-order splitting writes the four-bit `arr[0]` cell and
the one-bit output from one sampled five-bit RHS; the second assignment reads
the same cell back, including x propagation. Dynamic, aliased and overlapping
array leaves remain loud, and the legacy corpus census is unchanged.

The `fixed_array_noncanonical_slice` fixture composes the two normalizations:
the constant cell `arr[0]` is emitted first, then its `[10:9]` element slice
maps to the cell offsets `[3:2]`. The runner observes `11xx` and `x0xx` on the
whole cell; dynamic packed bounds remain loud and no new storage is needed.

The `fixed_array_reverse_range` fixture checks a descending unpacked range
`[1:0]`. Declaration order remains `arr[1]`, `arr[0]`, but the literal `arr[0]`
write and read target the `arr[0]` cell and preserve the same `0`, `1`, `x`
trace. This keeps source labels visible instead of substituting ordinal
positions.

## Extractor robustness notes (observed, not fixed)

1. **Zero crashes.** 21,307 single-file compiles (including 1,747
   deliberately-illegal `compile_error` tests): 0 pipeline exceptions,
   0 `ExtractorInternal:*` nodes, 0 per-file timeouts. The "never fails on
   valid SV" guarantee empirically extends to invalid SV.
2. **`clean` does not imply valid SV.** `extract.py` never consults
   compilation diagnostics, so 18 of the 29 clean files are
   `:type: compile_error` negative tests (e.g.
   `chapter-10/10.3.2--variable-only-one-continuous-assignment-driver.sv`:
   two continuous assigns to one variable — illegal, but every node is M0
   vocabulary). Any conformance harness built on envelopes must gate on
   `:type:` (or on slang diagnostics) before trusting a clean envelope.
3. **Signedness is explicit in the M0 envelope.** Signed four-state ports,
   variables and nets retain `signed: true`; order comparisons whose two
   elaborated operands are signed are emitted as `s<`, `s<=`, `s>` or `s>=`.
   The M0 value core interprets those tags as two's-complement comparisons and
   still collapses any x/z operand to x. Unsigned comparisons keep their
   existing tags and behavior. This closes the former `type_width` refusal and
   the `-1 < 0` mis-evaluation boundary without inferring signedness from
   names at runtime.
4. **`InvalidStatement` clusters on unknown system calls**: 797 simulation
   files carry it, 313 of them as their *only* adapter-residual blocker —
   overwhelmingly slang marking statements bad around system functions it
   doesn't accept in that form (`$abs(-5)`, `$test$plusargs(vector)`, …).
   These are slang-frontend conformance gaps, not extractor bugs; they cap
   the reachable suite regardless of Lean-side work.
5. **Multi-file tests**: 29 files use real `` `include `` directives (27 in
   chapter-22). `extract.py` compiles single files with no include path, so
   the census skips them with reason rather than misclassifying a partial
   parse. Supporting them needs an include-dir argument in `extract.py`
   (one-line `SyntaxTree.fromText` change) — deferred.

## Artifacts

**CORRECTED 2026-08-23** (quality audit HIGH, `docs/quality-audit-2026-08-23.md`
§sv). This section previously named `harness/sv/conformance/census.json` as
"the summary block backing every table above" — a file that **`.gitignore`
line 5 excludes**, so it is absent from every checkout. A table whose backing
artifact cannot be obtained is a number about nothing, and the exclusion was
worse than an oversight because it looked deliberate.

* **`docs/sv-construct-census.json` — THE COMMITTED ARTIFACT, and what
  every table above should be read against.** Provenance + summary block,
  20 295 bytes, sorted and indent-stable so a double run is byte-identical.
  It carries the corpus name and path, file count, walk mode, frontend
  FAMILY (`pyslang-11`, never a point release), platform and python version,
  because a census that cannot say what it measured is not a measurement.
  `--compare` checks it against a fresh run and **exits non-zero on any
  drifting key**.
* `extractors/sv/census.py` — the census tool (python3.12 + pyslang 11.x;
  `--corpus-name`, `--corpus`, `--all-dirs`, `--recheck`, `--compare`,
  `--limit`, `--jobs`). Regenerate both artifacts with:

      python3.12 extractors/sv/census.py --corpus-name sv-tests-2

* `harness/sv/conformance/census.json` — the **per-file** records, ~11.9 MB
  over 21 186 files. **Deliberately not committed**: this repository's
  census artifacts run 6 KB–773 KB, so the per-file half stays
  regenerable-by-the-line-above while the half every claim actually cites is
  the committed summary. Its exclusion is now a stated policy rather than a
  silent `.gitignore` entry.
* `harness/sv/conformance/unlockable.txt` — **0 bytes on this host, and that
  is a measured finding rather than a missing file.** This document was
  written when it held 11 ch-4/6/11 paths. Re-measured 2026-08-22: **two of
  those eleven files no longer exist in the corpus; the other nine do and no
  longer classify as unlockable.** `classify()` was verified
  **byte-identical** to the committed version function-by-function, so this
  is a corpus-or-host difference and **not a regression** — the landed set
  was measured on Linux, this one on `darwin-arm64`. Recording it is the
  point: with no provenance stamp there was no way to tell those three
  causes apart, which is why the stamp now exists.

**One further staleness this correction exposes**: the counts above were
taken over **21 336** chapter files; the corpus today walks **21 186**. The
tables are therefore accurate as of their census date and not as of this
checkout — which is exactly what `--compare` is for, and why it now exits
non-zero rather than reporting agreement it cannot support.


### Type-directed packed selected reads — 2026-10-20

Supported two-state integral vectors and whole untagged packed structs/unions
now reuse the legacy selected-read operation. Invalid selected positions are
zero for a two-state whole source and x for a four-state whole source; partial
overlap retains valid bits. Mixed-field aggregates use their whole state kind.
The lowering applies two-state conversion to the result, preserving unsigned
selection and the existing constant-only noncanonical-range normalization.
Dynamic/effectful and unsupported aggregate shapes retain their prior limits;
the symbolic selected-read path is unchanged.

On the SAME **22,035** chapter paths, the paired census reports **3,018 → 3,054
clean**, **18,951 → 18,915 partial**, **66 include skips** and **zero extraction
errors**, with **37 gains** and **one loss**. The loss closes a prior false admission
of named string control escapes `\a`, `\v` and `\f`, whose decoded values
disagree with the simulator; those spellings now refuse before resize folding.
The authored `selected_types` fixture and 34 newly clean time-zero files match
complete simulator output in value-preserving mode. A further timed NBA-loop
file agrees through the existing scheduler. Two newly clean files remain loud
in the time-zero runner because they need delay or continuous-process support. Default-mode probes disagree on partial invalid reads,
so this comparison does not assert default-mode agreement there. Three
fixture-bound kernel theorems cover unknown-index zero fill and symbolic
partial overlap for both source state kinds. No evaluator or scheduler changed.


### Time-zero query boundary — 2026-10-20

A fresh paired **22,035**-path extraction census is unchanged: **3,054 clean**,
**18,915 partial**, **66 include skips**, zero errors and zero changed rows.
The runtime loader now preserves existing `time_zero` literal provenance as
design-level metadata and refuses it at the timed boundary. Time-zero
execution and ordinary literal timed execution remain available. The
previously extraction-clean delayed packed-struct corpus fixture continues
to refuse in the self-check runner and now also refuses explicitly in the
timed loader, closing its constant-zero `$time` leak. This is a corrected
admission boundary, not additional corpus runtime coverage.
