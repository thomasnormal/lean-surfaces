# Event controls over expressions — repricing boundary

IEEE §9.4.2 permits an event control to sample an expression, not only a
single-bit identifier. A value-change event wakes when the sampled expression's
value changes. `posedge`, `negedge` and `edge` apply the four-state edge rules
to the expression result; for a multibit result, the edge decision uses its
least-significant bit. Concatenations, reductions, conditionals, operators and
selected values are evaluated before the event is registered, and the sampled
value is retained for later comparisons. The control re-arms at the same
continuation after a wake.

## Why expression event controls remain a boundary

The public envelope carries only the simple event form whose edge operand is a
one-bit identifier. It has no expression sampler, dependency set, retained
previous result, four-state edge conversion or aggregate-to-singular
validation. Reducing `@(a | b)` to one operand, treating a concatenation as a
single signal without sampling it, or selecting a fixed bit of a vector would
change both wake-up conditions and re-arming behavior. The tier therefore
keeps `SignalEventControl:clock` loud and introduces no second scheduler.

## 2026-10-22 census and decision

The fresh **22,035**-path census records `SignalEventControl:clock` in **350**
files: **20** are event-expression-only and **330** co-occur with another
wall. Repricing the sole files finds **20** spans. Four are multibit edge
controls whose least-significant bit matters; **16** are value-change controls.
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
