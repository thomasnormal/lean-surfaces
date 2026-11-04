# Event controls over expressions — repricing boundary

IEEE §9.4.2 permits an event control to sample an expression, not only a
single-bit identifier. A value-change event wakes when the sampled expression's
value changes. `posedge`, `negedge` and `edge` apply the four-state edge rules
to the expression result; for a multibit result, the edge decision uses its
least-significant bit. Concatenations, reductions, conditionals, operators and
selected values are evaluated before the event is registered, and the sampled
value is retained for later comparisons. The control re-arms at the same
continuation after a wake.

Timed `always_ff` now uses the same sampled-expression registration as plain
timed `always` for packed clocks. A vector clock such as
`always_ff @(posedge bus)` and a selected clock such as
`always_ff @(posedge bus[0])` are compared at each publication, with the edge
decision applied to the result's least-significant bit. The
`always_ff_expression_clock` witness covers both forms. Real, chandle,
aggregate, guarded, and otherwise unsupported clock expressions remain loud;
three-event lists remain a separate boundary.

## Real-valued event expressions — 2026-10-31

`always @(r)` where `r` is a `real` remains a loud boundary. The flat
`SvState` stores four-state packed vectors, not real payloads or their exact
event-equality rules, so the extractor records `SignalEventControl:clock`.
The `event_real_refuse` fixture pins this refusal; adding a scalar placeholder
would fabricate wakeups for real changes.

## Unpacked-array singular event expressions — 2026-10-31

An event expression can be syntactically singular while still selecting an
element of an unpacked aggregate, as in `always @(arr[2])` for
`logic [7:0] arr[4]`. The flat `SvState` has no unpacked-array element store,
so the extractor records this `SignalEventControl:clock` form as a loud
boundary. The `event_aggregate_singular_refuse` fixture and differential row
pin that refusal; the aggregate store and its sampled event value must arrive
together before this form can wake and re-arm faithfully.

Before packed-identifier admission, the read-only repricer found **15** sole
event-expression files and instances; the singular-or-aggregate feature
accounted for **1** of them. This item adds no scheduler shortcut and leaves
the existing packed-select and packed-expression registrations unchanged.

## Packed-identifier event expressions — 2026-10-31

Plain timed events now retain a packed identifier directly, including
`always @(bus)` and `always @(posedge bus)` for a four-bit `bus`. The scheduler
compares the sampled vector for value-change events and applies `posedge` or
`negedge` to its least-significant bit, so changes in higher bits alone do not
wake an edge-qualified process. The
`always_event_multibit_posedge` witness follows the IEEE §9.4.2 sequence and
observes exactly one wake across three vector changes.

The opposite edge uses the same sampled result: `always @(negedge bus)` applies
`negedge` to the packed identifier's least-significant bit. The
`always_event_multibit_negedge` witness covers two falling transitions and
higher-bit changes that leave the edge result unchanged.

Plain timed controls also retain the explicit `edge` spelling, for example
`always @(edge bus)`. In the current packed timed slice it uses the existing
any-value-change registration; the `always_event_explicit_edge` witness covers
all four changes. The clocked `always_ff` contract and four-state edge-specific
diagnostics remain separate.

Event lists use the same mapping per member: `always @(edge a or edge b)`
registers both scalar signals for any change. The
`always_event_explicit_edge_list` witness covers four alternating changes.
Per-member guards are retained too; `always_event_explicit_edge_list_iff`
covers a disabled change followed by three guarded list-member transitions.
Comma-separated lists use the same registration; the
`always_event_explicit_edge_comma_list` witness covers the equivalent four
changes with `always @(edge a, edge b)`.
Comma-separated members retain their guards too; the
`always_event_explicit_edge_comma_list_iff` witness covers a disabled change
followed by three guarded transitions.
An explicit edge can also carry the existing scalar guard: the
`always_event_explicit_edge_iff` witness covers a disabled change followed by
two guarded transitions.
The same guard applies to sampled operators; the
`always_event_binary_explicit_edge_iff` witness covers a disabled binary-result
change followed by two guarded transitions.
The ternary form follows the same path; `always_event_ternary_explicit_edge_iff`
covers a disabled selected-result change followed by two guarded transitions.
Concatenations use it too; `always_event_concat_explicit_edge_iff` covers a
disabled concatenated-result change followed by two guarded transitions.
Reductions use the same guarded path; `always_event_reduction_explicit_edge_iff`
covers a disabled reduction-result change followed by two guarded transitions.
Logical-not results use it as well; `always_event_logical_not_explicit_edge_iff`
covers a disabled zero/nonzero change followed by three guarded transitions.
Bitwise-not results use the same guarded path;
`always_event_bitwise_not_explicit_edge_iff` covers a disabled vector-result
change followed by two guarded transitions.
Dynamic bit-selects use it too; `always_event_dynamic_bit_select_explicit_edge_iff`
covers a disabled selected-bit change followed by two guarded transitions.
Dynamic part-selects use the same guarded path;
`always_event_dynamic_part_select_explicit_edge_iff` covers a disabled selected
vector change followed by three guarded transitions.
Descending dynamic part-selects use it as well;
`always_event_dynamic_part_select_desc_explicit_edge_iff` covers a disabled
selected-vector change followed by three guarded transitions.

The same registration applies to sampled operators, for example `always
@(edge (a | b))`. The `always_event_binary_explicit_edge` witness covers four
changes in the binary result.
Packed ternaries use it as well: `always @(edge (sel ? a : b))` wakes on every
selected-result change; `always_event_ternary_explicit_edge` covers branch and
operand changes.
Concatenations use the same path: `always @(edge {a, b})` wakes on each
concatenated-result change, covered by `always_event_concat_explicit_edge`.
Reductions also use it: `always @(edge |bus)` wakes when the scalar reduction
result changes, covered by `always_event_reduction_explicit_edge`.
Logical-not results use it as well: `always @(edge !bus)` wakes on each
zero/nonzero transition, covered by
`always_event_logical_not_explicit_edge`.
Bitwise-not results use it too: `always @(edge ~bus)` wakes on every sampled
vector change, covered by `always_event_bitwise_not_explicit_edge`.

This admission is for the sampled-expression `always` path. `always_ff` keeps
its separate one-bit clock contract; computed selectors and aggregate event
operands remain loud.

## Dynamic packed bit-select event expressions — 2026-10-31

Plain timed events now retain a dynamic packed bit-select such as
`always @(bus[idx])`. The sampled `SelectRead` expression is evaluated in the
old and newly published states, so a change to the selected bit wakes the
process and an index change wakes it only when the selected result changes.
The `always_event_dynamic_bit_select` witness covers both bus and index
updates through the same event-expression registration.

An edge qualifier uses that same sampled result: `always @(negedge bus[idx])`
applies `negedge` to the selected bit after each index or source update. The
`always_event_dynamic_bit_select_negedge` witness covers two selected-bit
falling transitions and ignores an intervening rising transition.
The explicit `edge` spelling uses the same any-change registration;
`always_event_dynamic_bit_select_explicit_edge` covers source and index changes
that produce four selected-result transitions.

Computed dynamic bases and unpacked aggregate elements still need a
range-aware or aggregate-backed dependency store and remain loud.

## Direct dynamic packed part-select event expressions — 2026-10-31

Plain timed events now retain a direct dynamic packed part-select such as
`always @(bus[base +: 2])` when the base is a single identifier. The sampled
`SelectRead` result is compared across publications, so changing the source
bits or moving the base wakes the process according to the selected vector.
The `always_event_dynamic_part_select` witness covers both changes through the
same registration.

The sampled vector also accepts an edge qualifier: `always @(posedge
bus[base +: 2])` applies `posedge` to the selected vector's least-significant
bit. The `always_event_dynamic_part_select_posedge` witness covers source and
base changes, with only two result-LSB rising transitions waking the process.
The explicit `edge` spelling uses the same any-change registration;
`always_event_dynamic_part_select_explicit_edge` covers source and base changes
producing five selected-result transitions.

Computed base expressions, partial or out-of-range aggregate selections, and
unpacked array elements remain loud.

## Vector unary event expressions — 2026-10-31

Bitwise inversion over a packed vector is now retained as a sampled event
expression, for example `always @(~bus)`. The complete unary result is
compared across publications, so a change in any operand bit can wake the
process. The `always_event_vector_unary` witness covers two result changes;
logical `!` remains in the scalar-result vocabulary.

The sampled vector result also accepts an edge qualifier: `always @(posedge
~bus)` applies `posedge` to the inverted result's least-significant bit. The
`always_event_vector_unary_posedge` witness covers source changes that leave
that bit unchanged and two transitions that wake the process.

## Vector binary event expressions — 2026-10-31

Packed `&`, `|`, and `^` event expressions now retain their complete result,
for example `always @(a | b)` with two-bit operands. Operand changes that do
not change the binary result do not wake the process. The
`always_event_vector_binary` witness covers both unchanged and changed
results.

## Vector ternary event expressions — 2026-10-31

Scalar-condition ternaries now retain packed results, for example
`always @(sel ? a : b)` with two-bit branches. The selected vector is sampled
before and after each publication, so branch and condition changes wake the
process only when the resulting vector changes. The
`always_event_vector_ternary` witness covers both selected branches.

Logical negation over a packed vector is also retained as a scalar sampled
result, as in `always @(!bus)`. The vector's truthiness is evaluated before and
after publication; `always_event_vector_logical_not` covers zero/nonzero
transitions.

The same sampled scalar result accepts an edge qualifier: `always @(posedge
!bus)` applies `posedge` to the logical-not result, so a nonzero-to-zero vector
transition wakes the process. The `always_event_vector_logical_not_posedge`
witness covers both result transitions through the existing edge registration.

## Named-event expressions — 2026-10-31

`always @(evt)` where `evt` is a declared named event remains loud. Named
events require an event-object queue and trigger identity, neither of which is
represented by the packed `SvState` or the retained sampled-expression path.
The `event_named_refuse` fixture records this `SignalEventControl:clock`
boundary.

## Mixed expression/scalar event lists — 2026-10-31

An event list that combines a sampled expression and a scalar signal, such as
`always @(a | b or c)`, remains loud. The current scheduler has separate
registrations for scalar edge lists and sampled-expression lists; accepting
the mixed shape would undercount wakeups. The
`always_event_mixed_expression_list` fixture records the refusal until one
combined dependency registration is available.

## Procedural expression waits — 2026-10-31

A standalone procedural wait such as `@(a ^ b);` inside an `initial` body
remains loud. It needs a retained continuation and sampled-expression
registration at statement level, rather than the process-level `always` path.
The `event_wait_expression_refuse` fixture records this
`SignalEventControl:clock` boundary.

## Edge-qualified packed binary events — 2026-10-31

`always @(posedge (a | b))` now uses the sampled binary result and applies the
existing four-state edge rule to its least-significant bit. The
`always_event_binary_posedge` witness covers higher-bit-only changes followed
by one result-LSB transition.

Ternary packed results use the same rule: `always @(posedge (sel ? a : b))`
applies `posedge` to the selected result's least-significant bit. The
`always_event_ternary_posedge` witness covers branch selection and two result
edges.

`always @(h)` where `h` is a `chandle` remains loud because IEEE 1800-2023
§6.14 forbids chandle values in event expressions and the model has no opaque
handle identity. The `event_chandle_refuse` fixture pins this refusal.

## Constant bit-select events — 2026-10-31

Plain `always` events over a one-bit constant packed select, such as
`always @(bus[2])`, now retain the `SelectRead` expression. The scheduler
evaluates it in the old and newly published states, wakes on a changed sampled
value, and re-arms the same continuation through the existing event loop.
Computed dynamic selectors and unpacked aggregate elements remain loud until
their dependency storage and sampled-value rules are represented.

The read-only corpus repricer now finds **7** sole
`SignalEventControl:clock` files and **7** spans, down from **27/27**; the
`always_event_bit_select` witness covers the retained value-change path.

Edge-qualified constant selects use the same sampled registration. For
`always @(posedge bus[2])`, the scheduler applies `posedge` to the selected
value's least-significant bit and re-arms after the body; the
`always_event_bit_select_posedge` witness covers a 0-to-1 selected-bit edge.
The `always_event_bit_select_negedge` witness covers the corresponding 1-to-0
selected-bit transitions.
The `always_event_part_select` witness covers a whole-vector value change.
The `always_event_part_select_posedge` witness covers a 0-to-1 transition of
the selected vector's least-significant bit; the existing sampled-expression
edge rule applies to the complete packed result.
The `always_event_part_select_negedge` witness covers the corresponding
1-to-0 transitions while higher-bit changes remain quiet.
The `always_event_conditional` witness covers a selected-branch value change.
Scalar binary `&`, `|`, and `^` expressions use the same result comparison;
the `always_event_binary` witness covers operand changes that leave `a | b`
unchanged and changes that alter it.
Reduction `|`, `&`, and `^` events use the same scalar result comparison; the
`always_event_reduction` witness covers a reduction result transition.
The `always_event_reduction_posedge` witness covers `posedge` on a reduction
result's scalar transition.
Unary scalar `~` and `!` events use the same result comparison; the
`always_event_unary` witness covers a unary result transition.
Concatenation events compare the complete packed result; the
`always_event_concat` witness covers a concatenated value change.

Packed concatenations use the same edge rule: `always @(negedge {a, b})`
applies `negedge` to the concatenation's result LSB. The
`always_event_concat_negedge` witness covers a higher-bit-only change and one
result-LSB transition.

## Why expression event controls remain a boundary

The public envelope carries sampled expressions for packed identifiers,
constant and direct dynamic packed selects, scalar ternaries, binary and
reduction operators, unary operators, and concatenations. Dynamic
computed selectors and unpacked aggregate elements still need dependency storage,
retained previous results, four-state edge conversion, and
aggregate-to-singular validation. Reducing
`@(a | b)` to one operand, treating a concatenation as a single signal without
sampling it, or selecting a dynamic part of a vector would change both wake-up
conditions and re-arming behavior. The tier keeps those
`SignalEventControl:clock` forms loud and introduces no second scheduler.

## 2026-10-22 census and decision

The fresh **22,077**-path census records `SignalEventControl:clock` in **350**
files: **27** are event-expression-only and **323** co-occur with another
wall. Repricing the sole files finds **27** spans before the constant-select
admission. Four are multibit edge controls whose least-significant bit matters;
**23** are value-change controls.
The spans include **3** binary expressions, **1** concatenation, **1**
conditional expression, **3** reduction or unary expressions, **3** selected
expressions, **4** singular/aggregate cases, **11** result-change scenarios
and **1** scheduler-context row (features overlap).

Representative sole rows include:

* `chapter-9/9.4.2--edge-detected-only-on-lsb.sv`
* `chapter-9/9.4.2--event-any-change-non-edge.sv`
* `chapter-9/9.4.2--event-concat-expression-result-change.sv`
* `chapter-9/9.4.2--event-conditional-expression-result-change.sv`
* `chapter-9/9.4.2--event-reduction-expression-result-change.sv`
* `chapter-9/9.4.2--event-control-part-select-result-change.sv`
* `chapter-4/4.4--time-slot-has-17-ordered-regions.sv`

Reproduce the table with:

```text
python3.9 extractors/sv/event_expression_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it classifies expression shapes in unsupported
event controls without registering a wake-up or choosing a sampled value.
