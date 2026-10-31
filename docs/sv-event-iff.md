# Conditional event (`iff`) boundary — retained wait qualification

`SignalEventControl:iff` marks an event control whose trigger is qualified by
 an `iff` condition. The event must occur first and the guard is sampled when
 that event arrives; changing the guard alone does not wake the process. The
 timed slice admits scalar identifier, comparison, and logical guards on plain
`always` events, positive- or negative-edge `always_ff` clocks, and both events
of a two-edge asynchronous-reset `always_ff`; constant-index packed selects
and ascending dynamic packed part-selects such as `en[i +: 2]` are also
admitted. The marker remains explicit for unsupported expressions.

## Why the remaining conditional event controls stay loud

IEEE 1800-2023 §§9.2.2.4 and 9.4.2.3 make the guard part of event
registration, wake-up filtering and re-arming. The retained event-list
registration now carries a side-effect-free scalar guard and applies it at the
publication point. The retained evaluator covers identifiers, literals,
constant-index packed selects, ascending dynamic packed part-selects, scalar
equality/inequality comparisons, and logical `&&`/`||` combinations; calls,
descending dynamic or aggregate selects, and other general expressions still
need a broader evaluator. `always_ff` guards
remain on the clock registration and preserve its inferred-clock and
single-driver rules. In a guarded clock-plus-reset list, `iff` filters the
clock edge and `reset_iff` filters the reset edge independently. No second
scheduler or guessed guard evaluation is introduced.

## Guarded asynchronous-reset lists — 2026-10-31

`always_ff @(posedge clk iff en or negedge rst_n)` now retains the scalar guard
on the clock event while keeping the asynchronous reset edge unconditional.
The reset edge therefore still wakes the process when `en` is false, and a
clock edge wakes it only when the guard is true. Active-high `areset` uses the
same representation with its positive reset polarity. A scalar guard attached
to the reset event is retained in `reset_iff` and sampled at that reset edge.

The `always_ff_async_reset_iff` witness exercises a disabled clock edge, an
unguarded reset edge, and an enabled clock edge through the existing scheduler.

## Guarded asynchronous-reset edges — 2026-10-31

The envelope now retains `reset_iff` for a scalar guard on the reset event,
such as `negedge rst_n iff en`. The existing `resetGuard` field samples it at
the reset publication; no clock guard is implied. The
`always_ff_async_reset_iff_reset` witness first publishes a disabled reset edge
and then an enabled one.

## Indexed scalar guards — 2026-10-31

The guard slice now admits a direct one-bit packed-vector select such as
`iff en[0]`. The selected value and its scalar literal or identifier index are
evaluated by the existing `SelectRead` expression path at publication. Part
selects, dynamic or aggregate selectors, calls, and other unsupported shapes
remain loud.

The `always_ff_async_reset_iff_bit` witness checks a disabled bit-select clock
edge, an unconditional reset edge, and an enabled clock edge.

## Constant packed-vector guards — 2026-10-31

The same `SelectRead` path now admits a constant-index packed-vector guard such
as `iff en[1:0]`; `eventGuardPass` uses the vector's ordinary truthiness, so any
known `1` wakes the process. Dynamic indexed part-selects and aggregate
selectors remain loud. The `always_ff_event_iff_vector` witness covers a zero
vector followed by a one-containing vector.

Ascending dynamic packed part-selects such as `iff en[idx +: 2]` use the same
fueled `SelectRead` evaluator and vector truthiness. Descending dynamic
part-selects remain loud until their direction rule is pinned. The
`always_ff_event_iff_dynamic` witness covers a disabled edge followed by an
enabled ascending dynamic slice.

Descending dynamic packed part-selects such as `iff en[idx -: 2]` now use the
same evaluator and truthiness. The `always_ff_event_iff_dynamic_neg` witness
covers the disabled and enabled descending slices.

## Scalar comparison guards — 2026-10-31

The timed slice now retains `iff en == 1'b1`, `iff en != 1'b0`, and the
case-equality variants when both sides are scalar, side-effect-free expressions.
The guard is evaluated with the same four-state expression rules as the body;
an unknown result does not wake the process. The `always_ff_event_iff_cmp`
witness exercises a disabled edge followed by an enabled comparison and
MATCHes. Indexed, called, and otherwise unsupported guards remain loud.

The read-only corpus repricer after this admission reports **6** sole
`SignalEventControl:iff` files and **6** spans (down from 7/7); one remaining
`always_ff` span is still outside this scalar guard vocabulary.

## Scalar logical guards — 2026-10-31

Logical `iff en && mode` and `iff en || mode` guards now use the same
four-state truth table as process conditions. An unknown result does not wake
the event registration. The `always_ff_event_iff_logic` witness checks a
disabled logical guard followed by an enabled edge and MATCHes; calls, selects,
and other unsupported expressions remain loud.

## 2026-10-22 census and decision

The fresh 22,043-path census records `SignalEventControl:iff` in **7** files;
all **7** are sole refusals. Re-elaborating those rows with the read-only
repricer finds **7** qualified event spans:

| source shape | spans | files |
|---|---:|---:|
| procedural event `iff` | 4 | 4 |
| `always_ff` `iff` | 2 | 2 |
| procedural `always` `iff` | 1 | 1 |
| edge-qualified `iff` | 3 | 3 |
| level-qualified `iff` | 4 | 4 |

The labels overlap by design. Reproduce the table with:

```text
python3.9 extractors/sv/event_iff_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument re-elaborates source in memory and writes no output beside the
read-only corpus. Its shape counts are telemetry, not a wait evaluator.
