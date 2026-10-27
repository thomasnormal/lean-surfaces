# Assignment targets — admitted boundary

This document fixes the public boundary for SystemVerilog assignment left-hand
sides (`AssignmentExpression:target`). It applies to the legacy/self-check
envelope and to the symbolic `sv-0.2` envelope. The rule follows the IEEE
1800-2023 assignment and packed-data clauses (10–11): evaluate the right-hand
side once, then update the selected destination in the order required by the
owning execution path. A target is admitted only when its destination can be
represented by the existing scalar, packed-vector, or expanded fixed-cell
state.

## Admitted representations

The legacy path admits a whole identifier, a packed bit or part select over an
identifier, and a direct field window of an untagged packed struct or packed
union. A constant element of an eligible one-dimensional fixed-unpacked array
is emitted as its own vector-cell identifier. The same path admits the
already-tested direct concatenation and right-streaming forms when every leaf
is one of those fixed destinations and the source width is definite. Select
indices and source expressions must remain in the pure integral subset; an
effectful selector or right-hand side is retained as `Unsupported`.

The legacy path also admits a finite dynamic-array `with [base +: count]`
stream target when the array has one constant allocation and `count` is an
integral variable assigned exactly once from a literal before the stream. The
extractor samples that source-ordered extent and lowers the selected cells
individually; control-dependent or reassigned extents remain outside this
representation.

The symbolic path carries `Ident`, `BitSel`, and `PartSel` targets over an
identifier. Its continuous-assignment slice additionally admits a nested
concatenation of direct scalar, constant bit-select, or constant part-select
leaves. `Design2` samples one right-hand side and applies fixed windows to the
existing vector state. Fixed-array cells can be leaves after declaration
expansion. These symbolic continuous forms are deliberately separate from the
legacy/self-check runner, whose loader has no continuous-driver scheduling
rule.

## Refusal boundary

The target conversion stays loud for destinations that need a representation
the public tier does not have:

* dynamic, unbounded-associative, queue, multidimensional, or otherwise
  unpacked aggregate storage (finite literal-key associative cells and the
  literal queue size-mismatch halt below are narrow exceptions);
* keyed/default/replicated aggregate patterns outside the admitted fixed-cell
  lowering, and whole aggregate copies without a cellwise snapshot rule;
* nested, unpacked, tagged, class, interface, or hierarchical members outside
  the direct packed-window case;
* dynamic or effectful select bounds and streaming forms with a direction or
  slice size outside the admitted subset (constant indexed `with` ranges over
  ascending fixed cells, plus the single-assignment literal dynamic extent,
  are admitted); and
* legacy continuous assignments whose target needs a continuous-driver,
  update-region, or net-resolution rule.

No target family is admitted by manufacturing an aggregate store or by adding
a second scheduler. A future target rung must first supply the missing storage
or the scheduler-facing continuous-assignment rule, then add a source-bound
fixture and an independent simulator comparison.

## Literal queue-to-fixed-array size mismatch — 2026-10-27

When a direct queue declaration has only scalar literal elements and a blocking
copy targets a fixed unpacked integral array with a different element count,
the extractor lowers the §7.6 run-time error to the existing immediate
`$finish`. Earlier scalar output is retained and no queue or aggregate storage
is introduced. Equal-size copies use the existing left-to-right cellwise
lowering; dynamic, aliased, mutated, aggregate, timed, and nonblocking forms
remain `AssignmentExpression:target`.

The `queue_fixed_size_mismatch` fixture supplies the `BEFORE` differential
transcript and Lean receipt. The current 22,064-path census moves **5,325 →
5,326 clean / 16,672 → 16,671 partial** (67 include skips), while the target
wall falls **2,844 → 2,842**.

## Finite associative-cell presence — 2026-10-27

Finite literal-key associative arrays now carry one flat value cell and one
two-state presence bit for each observed key. A blocking or nonblocking element
write updates both cells, and `exists(key)` reads the exact presence bit, so an
absent key remains false even when its value cell has the element type's default
value. The admission is shared by string and integral keys and remains limited
to literal keys with scalar or packed-integral elements. Dynamic keys, whole
array aliases, `delete`, other methods, aggregate elements, and continuous
drivers stay loud; no associative object or scheduler state is fabricated.

The `assoc_exists_cells` fixture covers an empty query, value writes,
`exists`, and a compound element write; `assoc_exists_dynamic_refuse` pins the
dynamic-key boundary. The capped 22,059-path census moves **5,298 → 5,301
clean** and **16,694 → 16,691 partial** (67 include skips), while
`AssignmentExpression:target` falls **2,852 → 2,845**. Differential coverage
grows by two rows (one match and one recorded refusal), with no disagreement.

## Bounded dynamic `$dist_uniform` fixed-array writes — 2026-10-27

The self-check surface now admits an assignment whose RHS is
`$dist_uniform(seed, 0, 1000)` and whose destination is a one-dimensional
finite fixed-unpacked integral array selected by a pure integral index. The
32-bit seed is updated and the selected flattened cell is written in the same
branch; repeated seeds therefore produce the same sequence while the update
remains explicit state rather than an invented random oracle. The admitted
slice requires a direct 32-bit variable seed, literal bounds `0` and `1000`,
and a 32-bit array element. Other bounds, seed expressions, aggregate or
dynamic storage, effectful selectors, and value-position random calls remain
loud.

`dist_uniform_array_target` supplies the repeatability fixture, extractor
regression, Lean receipt, and differential row. The 22,059-path census moves
**5,253 → 5,254 clean** and **16,739 → 16,738 partial** (67 include skips);
`AssignmentExpression:target` falls **2,853 → 2,852**. Differential coverage
grows **294/289/0/5 → 295/290/0/5** with no disagreements; grammar coverage
remains **218/95/123**.

## Pure conditional continuous drivers from literal source state — 2026-10-26

A whole packed-net driver whose conditional expression has only literal arms
and conditions with one direct literal initialization may be sampled at time
zero. The selected literal drivers then use the existing per-bit wire resolver,
covering the all-high-impedance case and the ordinary net-declaration driver
shape without introducing live driver state. Unknown conditions, source
changes, effectful expressions, strengths, and scheduler-visible forms remain
loud. The `continuous_conditional_history_drivers` fixture covers the admitted
shape; `wire_z_z_resolves_to_z` and `net_decl_assign_one_per_net_v4` are the
corpus witnesses.

## Selected continuous windows from one literal source write — 2026-10-26

A packed net's selected continuous drivers may read a variable with one direct
literal initialization, either a declaration initializer or a blocking write
in an `initial` block. The extractor snapshots each fixed source window and
feeds the existing per-bit literal-driver resolver, so overlapping windows
retain IEEE wire resolution without a live driver store. Dynamic selectors,
aliases, multiple source writes, effectful expressions, strength combinations,
and other scheduler-visible drivers remain loud. The
`continuous_selected_history_windows` fixture covers an overlapping bit and
part-select pair; `scalared_net_allows_bitselect` is the corpus witness.

## Dynamic noncanonical packed indexed slices — 2026-10-26

Dynamic `+:` and `-:` targets on noncanonical one-bit packed vectors now map
the runtime base label into the flat selected-write window. Ascending ranges
are converted to increasing flat offsets so both directions preserve the
source-order value and later readback; the pure signed 32-bit base restriction
remains. Simple dynamic ranges, effectful or unsigned bases, aggregate
targets, and unsupported forms remain loud; partial reads retain the selected
evaluator boundary. The
`packed_array_dynamic_part_select` fixture pins both indexed directions.

## Dynamic indexed slices over wide packed elements — 2026-10-26

Dynamic `+:` and `-:` targets over a nested packed array now normalize the
runtime outer label in whole inner-element chunks. A selected width is an
integral number of those chunks; ascending slices use the increasing flat
window and descending slices retain the evaluator's high-endpoint convention.
Effectful bases, aggregate receivers, and unsupported selections remain loud.
The `packed_array_dynamic_wide_slice` fixture covers both declared directions,
read/write aliasing, and the wide-element geometry.

## Dynamic noncanonical packed-element targets — 2026-10-26

A pure signed dynamic element target on a noncanonical one-bit packed vector
now uses the same declared-label-to-offset conversion as packed reads. For an
ascending range such as `logic [0:7] a`, `a[i] = value` maps the runtime index
from the right label and updates the cell later read through `a[i]`. The
existing 32-bit signed index restriction remains; unsigned or effectful
selectors, aggregate targets, and unsupported ranges stay loud. The
`packed_array_dynamic_target` fixture pins the ascending geometry and alias.

## Dynamic nested packed-element targets — 2026-10-26

A dynamic element target on a nested packed array with integral elements now
maps the declared packed label to a flat-vector offset by multiplying the
runtime outer index by the element width. The read and blocking-target paths
use the same normalization, including ascending and descending declared
ranges, so a write through `a[i]` updates the same cell read through `a[i]`.
Out-of-range, aggregate, effectful, nonintegral, and unsupported index forms
remain loud; no aggregate store or scheduler-facing driver is introduced.
The `packed_array_dynamic_index` fixture and the multidimensional extractor
regressions pin the admitted geometry and its aliasing behavior.

## 2026-10-21 census and decision

The fresh chapter-scoped corpus contains 22,043 paths. The target wall occurs
in 4,030 files: 43 are target-only and 3,987 co-occur with another refusal.
The most common companions are `VariableSymbol:2state` (3,215 files),
`CallExpression` (1,339), `ExpressionStatement:CallExpression` (1,240),
`NamedValueExpression:2state` (1,113), `MemberAccessExpression` (720), and
`ClassType` (639). Companion counts overlap because one file can carry several
refusals.

The target-only repricer reports 79 instances in those 43 files:

| target-only source shape | instances | files |
|---|---:|---:|
| whole aggregate/array target | 27 | 23 |
| dynamic element target | 32 | 9 |
| packed or unpacked part-select target | 14 | 5 |
| concatenated or streaming target | 3 | 3 |
| constant element/bit target | 2 | 2 |
| keyed/default/replicated or unpacked-array pattern RHS | 1 | 1 |

The file counts overlap only when a file contains more than one target shape.
The target-only rows mix procedural aggregate/slice/stream forms with
generated continuous drivers. Procedural rows require aggregate or runtime
index representation; continuous rows require the scheduler-owned driver
path. The measured target-only set therefore has no independently admissible
legacy subfamily in this item. Existing packed/select/concat tests remain the
acceptance evidence for the admitted matrix, while every residual shape stays
loud until its prerequisite is supplied.

The measurement is reproducible with
`python3.9 extractors/sv/target_reprice.py --corpus <corpus>/tests`; it reads
the source in process and writes no envelopes beside the corpus. The global
4,030/43/3,987 counts come from the paired census artifact described in
`docs/sv-corpus-coverage.md`.

## Single literal continuous net drivers — 2026-10-24

A single whole-net continuous assignment with a pure integral literal RHS is
lowered to the existing time-zero blocking assignment. With no future RHS
change, no second driver, and no selected target, this preserves the net value
observed by the initial-only self-check runner without adding a driver queue or
resolution rule. Dynamic RHS expressions, variable targets, selected targets,
and multiple drivers remain loud and continue to require the scheduler-owned
continuous-assignment path.

`constant_net_driver` is the differential witness. The lowering is deliberately
limited to one source `assign` for that net and an existing `Net` declaration;
it does not generalize continuous assignment semantics.

## Literal continuous fixed-array variable cells — 2026-10-24

A pure integral literal assigned continuously to one constant cell of a
one-dimensional fixed-unpacked variable is lowered to the existing time-zero
blocking write for that expanded cell. The source is required to name that
cell exactly once, so the lowering has no future reevaluation or driver
resolution. Net arrays, dynamic or effectful indices, nonliteral sources, and
multiple drivers remain loud.

`constant_array_cell_driver` is the differential witness. It reuses the
ordinary scalar-cell representation and interpreter path; no aggregate store
or continuous-driver queue is added.

## Literal continuous fixed-array net cells — 2026-10-24

A one-dimensional fixed-unpacked `wire` array with one pure integral literal
driver per constant cell is flattened to independent `Net` cells. The existing
time-zero assignment and per-cell literal-driver resolution then apply without
introducing an aggregate net store. Whole-array, dynamic or multidimensional
uses, non-integral leaves, and future or effectful drivers remain loud.

`constant_net_array_cell_driver` is the differential witness. Multiple literal
drivers to the same flattened cell still use the existing four-state net
resolution; the declaration remains a `Net`, rather than being treated as a
procedural variable.

## Literal continuous packed-variable drivers — 2026-10-24

A pure integral literal assigned continuously to one whole packed variable or
one constant bit/part-select of a packed variable is lowered to the existing
time-zero blocking write. The source target must occur once, so the result has
no future reevaluation or driver conflict. Dynamic sources and selections,
multiple drivers, and aggregate targets remain on the scheduler-owned boundary.

`constant_variable_driver` covers both the whole-vector and selected-window
forms through the existing scalar and packed-target interpreter operations.

## Disjoint literal continuous packed-net windows — 2026-10-24

Multiple continuous assignments to disjoint constant windows of one packed
wire are lowered independently to time-zero blocking writes when every source
is a pure integral literal. An overlapping window or any dynamic peer remains
loud; it needs per-bit net resolution and live driver updates. The
`disjoint_literal_net_windows` witness covers the admitted disjoint form.

## Static literal continuous packed-window resolution — 2026-10-24

The same fixed-window lowering now resolves overlapping literal drivers on one
packed wire per bit using the existing four-state table: `z` yields, equal
active values remain, and conflicts or `x` produce `x`. Dynamic peers,
out-of-range windows, strengths, and future source changes remain loud. The
`overlapping_literal_net_windows` witness checks both the conflict bit and the
unchanged bits.

## Constant out-of-bounds fixed-array writes — 2026-10-22

IEEE 1800-2023 §7.4.5 makes a write through a constant invalid index on a
fixed unpacked array a no-op. The legacy extractor now recognizes a fully
constant selection through every fixed dimension, checks the declared ranges,
and lowers an out-of-bounds write to `Empty`. The right-hand side must still
be in the existing pure integral expression subset; this avoids dropping an
effect while preserving the no-update rule. In-range and dynamic selections
continue through their ordinary cell or selected-target paths.

`fixed_array_oob` checks both an in-range write and an out-of-range write in
the self-check interpreter. The two corresponding corpus witnesses are
`chapter-7/7.4.5--array-oob-write-noop-v3.sv` and
`chapter-7/7.4.5--oob-write-is-no-op.sv`. No aggregate storage or scheduler
rule is introduced.

## Type-keyed enum defaults in packed-struct array targets — 2026-10-24

A whole fixed unpacked array of packed-struct elements may use the existing
cell expansion when its assignment pattern supplies one enum type key and a
literal scalar default. The frontend's nested pattern inventory is normalized
to the enum value and scalar field literal before the ordinary per-cell
blocking assignments are emitted. Dynamic or effectful keys/defaults,
non-integral fields, aliases, and aggregate shapes outside the fixed cells
remain loud.

`typed_default_array_pattern` is the differential witness. It covers both
array cells and checks the enum field and the scalar field after the whole
assignment.

## Explicit-slice right-streaming targets — 2026-10-24

Right-streaming unpack targets may carry a positive explicit integral slice
size, including the built-in `byte`, `shortint`, `int`, `integer`, `longint`,
and `time` type spellings. The admitted lowering requires every direct scalar
or flattened fixed-array leaf to have exactly that width and samples one
integral RHS into the existing `ConcatTarget` representation. Streaming
`with` clauses, mixed-width leaves, nested or dynamic targets, and any
non-integral or effectful form remain loud.

`streaming_slice_target` is the source-bound witness for the `byte` spelling;
the extractor tests also pin numeric slices and the mixed-width refusal.

## Named-type left-streaming targets — 2026-10-24

The same fixed-width rule applies to left-streaming targets when the slice is a
built-in integral type. `byte` and the other admitted named widths resolve to
their positive bit count before the existing low-chunk-first lowering reverses
the source chunks. Unsized streams, mixed-width leaves, `with` clauses, and
dynamic or nested targets remain loud.

`streaming_left_slice_target` is the source-bound witness for the named
`byte` form.

## Shallow unpacked-union member targets — 2026-10-24

An untagged unpacked union whose members are equal-width integral vectors now
uses one ordinary flat vector cell. Direct member reads and blocking writes
through any member therefore preserve the union's required aliasing. Tagged
unions, unequal-width or mixed-state members, nested aggregates, whole-union
assignments, and nonblocking/timed forms remain loud until their aggregate
state and scheduling rules are represented.

`unpacked_union_member` is the source-bound witness. The lowering reuses the
existing `Ident` target and value paths; it adds no aggregate store or second
scheduler.

## Shallow unpacked-union whole copies — 2026-10-24

A blocking assignment between two equal-width integral values of the admitted
shallow untagged unpacked-union shape now copies their shared flat vector cells
directly. The copy preserves aliasing when the destination is read through any
member. Tagged, mixed-width, initialized, member-to-whole, nonblocking, and
timed forms remain loud until their aggregate and publication rules exist.

`unpacked_union_copy` is the source-bound witness. The lowering reuses the
ordinary `Ident` value and blocking-assignment paths and introduces no union
object or second scheduler.

## Shallow unpacked-union whole-value comparisons — 2026-10-24

Whole values of the admitted shallow untagged unpacked-union shape now read
from their shared vector cell for `==`, `!=`, `===`, and `!==`. This preserves
the value and case-equality rules while keeping union arithmetic and other
aggregate operations loud. Scheduled reads and unsupported union shapes remain
outside the flat-cell representation.

`unpacked_union_equality` is the source-bound witness; it compares values
written through alternate members without adding aggregate storage.

## Shallow unpacked-union conditional values — 2026-10-25

A conditional expression whose two arms are equal-width integral values of the
admitted shallow untagged unpacked-union shape now selects between their shared
flat cells. The result keeps the ordinary `Ternary` value path; mixed shapes,
aggregate arms, scheduled operations, and union arithmetic remain loud.

`unpacked_union_conditional` is the source-bound witness.

## Shallow unpacked-union compound member updates — 2026-10-25

A blocking compound assignment through a direct member of the admitted shallow
untagged unpacked-union shape now performs its read-modify-write on the shared
flat cell. Selector evaluation remains the existing packed-member path;
nonblocking, timed, mixed-shape, and unsupported compound operators remain
loud.

`unpacked_union_compound` is the source-bound witness.

## Single literal continuous packed-bit drivers — 2026-10-24

A single continuous assignment to one constant packed bit or part-select is
lowered to the existing time-zero selected blocking assignment when its RHS is
an integral literal. The net has no competing driver and the selected window
is already represented by the flat state target. Dynamic RHS expressions,
multiple drivers, dynamic selections, and aggregate/streaming targets remain
on the scheduler-owned boundary.

`constant_net_bit_driver` is the differential witness; the multiple-driver
case remains covered by the refusal boundary.

## Static literal wire-driver resolution — 2026-10-24

Multiple continuous drivers on one wire are resolved at time zero when every
driver is a whole-net integral literal. Resolution is performed per bit using
the IEEE table: `z` yields to an active driver, equal active values remain,
conflicting values become `x`, and an `x` driver keeps the result unknown. The
resolved value is lowered to one flat assignment. Dynamic drivers, variable
drivers, selected windows, strengths, and future source changes remain loud.

`static_net_resolution` is the differential witness. The folded path is
restricted to declared nets, so a variable with multiple continuous drivers
continues to refuse rather than being treated as a resolved wire.

## Literal continuous `tri` drivers — 2026-10-24

A scalar or packed `tri` with a complete set of pure integral literal
continuous drivers uses the same time-zero four-state value as a `wire`.
The declaration remains a net and literal drivers still pass through the
existing per-bit `z`/equal/conflict/`x` resolution. Dynamic or effectful
drivers, strengths, delayed assignments, and future source changes stay loud;
the declaration is rejected unless every driver is in the literal subset.

`constant_tri_driver` is the differential witness. This admits a fixed net
value without manufacturing a live driver queue or treating `tri` as a
procedural variable.

## Explicit-strength literal continuous drivers — 2026-10-24

A single whole-net continuous driver written with an explicit strength pair,
such as `(strong1, strong0)`, is admitted when its RHS is a pure integral
literal. The fixed value lowers through the existing time-zero path; the
strength metadata is retained in the extracted process for diagnostics.
Strength-bearing selected targets, multiple strength drivers, dynamic or
effectful sources, and strengthened `tri` declarations with multiple or mixed
drivers remain loud because the current flat representation does not model
per-driver strength resolution.

`constant_strength_driver` is the differential witness. Multiple strengthened
drivers remain ordinary continuous assignments and therefore preserve the
existing refusal boundary.

## Single strengthened `tri` literal drivers — 2026-10-24

A `tri` with one explicitly strengthened whole-net driver and a pure integral
literal source now uses the same fixed four-state value as an ordinary single
driver. Since there is no competing driver, strength never affects the
resolved value and no per-driver state is needed. Selected targets, multiple
or mixed-strength drivers, dynamic/effectful sources, and delayed assignments
remain loud.

`constant_tri_strength_driver` is the differential witness; the extractor
tests keep multiple strengthened `tri` drivers on the declaration refusal
boundary.

## Single strengthened packed-select drivers — 2026-10-24

A single explicitly strengthened packed bit or constant part-select with a
pure integral literal source now lowers to the existing selected time-zero
write. Multiple strengthened selected drivers remain continuous assignments,
including disjoint windows, because the selected-driver lowering does not yet
carry strength metadata through its resolution checks. Dynamic or effectful
sources and aggregate targets remain loud.

`constant_strength_select_driver` is the differential witness; the focused
tests pin both the selected target and the multiple-driver refusal.

## Constant out-of-bounds writes to fixed-size dynamic arrays — 2026-10-24

An integral 2-state dynamic array with one constant `new[N]` allocation may
erase a constant out-of-range element write. The array has already been
expanded into flat cells, and IEEE 1800-2023 §7.4.5 makes the invalid write a
no-op. Dynamic indices, resizes, aggregate or effectful values, and reads stay
loud; no dynamic-array object or scheduler state is introduced.

`dynamic_array_oob_write` is the differential witness. The 22,048-path corpus
has no exact instance of this shape, so its census remains **4,816 clean /
17,166 partial / 66 include skips** with `AssignmentExpression:target` at
**3,035 files**; differential coverage moves **121/117/0/4 → 122/118/0/4**.

## Literal dynamic extents in streaming targets — 2026-10-25

The finite dynamic-array streaming rung now admits `{>> {a with [base +:
count]}}` when `count` has one unconditional literal assignment before the
stream. The extractor samples that value and reuses the flattened-cell stream
window; later writes, control-dependent assignments, and out-of-range counts
remain loud. The `streaming_dynamic_with_range` fixture covers the §11.4.14.4
shape. On the available 21,342-path snapshot, clean files move **4,861 →
4,862** and `AssignmentExpression:target` falls **2,794 → 2,793**.

## Empty queue pops into integral unpacked structs — 2026-10-25

When an uninitialized queue is popped and its element type is an untagged
unpacked struct whose leaves are scalar or packed integral fields, the default
element value is lowered to one zero/default write per flattened destination
cell. This follows §7.10.2.4's empty-pop result and §7.4.6's aggregate default
initialization while reusing the existing struct field-cell representation.
Queue mutations, aliases, nonempty queues, aggregate fields, and scheduled
forms remain loud.

`queue_empty_pop_struct_default` is the differential witness. In the 22,053-path
snapshot, clean files move **5,057 → 5,058**, partial files **16,929 → 16,928**,
and `AssignmentExpression:target` falls **2,937 → 2,936**; differential
coverage moves **203/198/0/5 → 204/199/0/5**.

## Whole bounded multidimensional fixed-array copies — 2026-10-26

Distinct bounded multidimensional unpacked arrays with integral leaves may be
copied cellwise in declaration order. Assignment-compatible arrays may use
different index labels when each dimension has the same ordinal extent. The
flat state already contains every leaf cell, so this lowering needs no
aggregate store and samples the complete source before writing the target.
Self-copies, mismatched extents, dynamic or aggregate leaves, and effectful
sources remain loud.

`fixed_array_nested_copy` is the differential witness; the current
22,058-path census remains **5,227 clean / 16,764 partial** with
`AssignmentExpression:target` at **2,857**.

## Constant multidimensional subarray copies — 2026-10-26

A constant prefix selection of a bounded multidimensional unpacked integral
array may copy into a distinct flat fixed array in declaration order. The
selected row is already represented by independent cells, so the lowering
samples those cells without an aggregate store. Dynamic selectors, overlapping
aliases, mismatched extents, aggregate leaves, and effectful sources remain
loud.

`fixed_array_subarray_copy` is the differential witness; the current
22,058-path census remains **5,227 clean / 16,764 partial** with
`AssignmentExpression:target` at **2,857**.

## Dynamic outer multidimensional subarray copies — 2026-10-26

A single dynamic outer index of a bounded multidimensional unpacked integral
array may now receive a distinct flat fixed-array row. The extractor expands
the finite outer range into guarded branches and copies each suffix cell in
declaration order, preserving descending labels and four-state values. Multiple
dynamic selectors, shape mismatches, aliases, aggregate leaves, timed forms,
and effectful sources remain loud.

`nested_fixed_array_dynamic_subarray_copy` is the differential witness; the
22,058-path census remains **5,227 clean / 16,764 partial** with
`AssignmentExpression:target` at **2,857**.

## Dynamic inner-prefix multidimensional subarray copies — 2026-10-26

The dynamic-prefix lowering now also admits one dynamic selector after a
constant prefix, such as `cube[0][index] = row`, while one or more trailing
dimensions remain omitted. Each finite branch copies the distinct flat source
row through the existing cell state in declaration order. Multiple dynamic
selectors, aliases, shape mismatches, aggregate leaves, timed forms, and
effectful sources remain loud.

`nested_fixed_array_dynamic_inner_subarray_copy` is the differential witness;
the 22,058-path census remains **5,227 clean / 16,764 partial** with
`AssignmentExpression:target` at **2,857**.

## Dynamic multidimensional subarray source reads — 2026-10-26

A single dynamic selector of a bounded multidimensional unpacked integral
array may now be read into a distinct flat fixed-array row. Finite selector
values become mutually exclusive `===` branches, and each omitted suffix
cell is copied in declaration order through the existing flat storage.
Multiple dynamic selectors, shape mismatches, aliases, aggregate leaves,
timed assignments, and effectful sources remain loud.

`nested_fixed_array_dynamic_subarray_read_copy` is the differential witness;
the 22,058-path census remains **5,227 clean / 16,764 partial** with
`AssignmentExpression:target` at **2,857**.

## Dynamic packed slices inside fixed-array cells — 2026-10-26

Dynamic `+:` and `-:` part-selects over a descending multidimensional packed
cell, such as `joe[7][i +: 2]`, now lower to the existing selected target and
read nodes. The runtime base is scaled by the inner packed-element width and
the descending form preserves its high-end position. Ascending packed ranges,
dynamic widths, aggregate cells, and effectful bases remain loud.

`fixed_array_dynamic_packed_slice` is the differential witness; the current
22,058-path census remains **5,227 clean / 16,764 partial** with
`AssignmentExpression:target` at **2,857**.

## Literal queue to fixed-array copies — 2026-10-27

A whole fixed unpacked array with scalar integral leaves now accepts a
blocking assignment from a queue whose initializer is an exact scalar-literal
sequence of the same length. The queue elements are expanded left to right
into the existing flat destination cells, matching §7.6's correspondence.
Mismatched sizes, later queue uses, aliases, aggregate elements, timed forms,
and nonblocking assignments remain loud because the flat state has no queue
object or runtime size diagnostic.

`queue_fixed_array_copy` is the differential witness and Lean receipt. The
22,059-path census moves **5,303 → 5,304 clean** and **16,689 → 16,688
partial**, while `AssignmentExpression:target` falls **2,845 → 2,844**.
Differential coverage moves **317/311/0/6 → 318/312/0/6** with no
disagreements; grammar coverage remains **218/97/121**.

## Exact fixed-array blocking self-copies — 2026-10-27

An exact whole-array blocking assignment to the same one-dimensional fixed
unpacked integral array is now lowered to `Empty`: every source cell is already
the corresponding destination cell, so the assignment has no observable
effect. Sliced or overlapping copies, nonblocking and timed forms, dynamic or
aggregate storage, and effectful sources remain at
`AssignmentExpression:target`; no aggregate snapshot or scheduler state is
introduced. The `fixed_array_self_copy` fixture supplies the `selfcopy 3 7`
receipt.
