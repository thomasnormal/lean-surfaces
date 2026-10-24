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

* dynamic, associative, queue, multidimensional, or otherwise unpacked
  aggregate storage;
* keyed/default/replicated aggregate patterns outside the admitted fixed-cell
  lowering, and whole aggregate copies without a cellwise snapshot rule;
* nested, unpacked, tagged, class, interface, or hierarchical members outside
  the direct packed-window case;
* dynamic or effectful select bounds and streaming forms with a direction or
  slice size outside the admitted subset (constant indexed `with` ranges over
  ascending fixed cells are admitted); and
* legacy continuous assignments whose target needs a continuous-driver,
  update-region, or net-resolution rule.

No target family is admitted by manufacturing an aggregate store or by adding
a second scheduler. A future target rung must first supply the missing storage
or the scheduler-facing continuous-assignment rule, then add a source-bound
fixture and an independent simulator comparison.

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
