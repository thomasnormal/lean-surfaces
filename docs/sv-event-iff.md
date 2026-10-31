# Conditional event (`iff`) boundary — retained wait qualification

`SignalEventControl:iff` marks an event control whose trigger is qualified by
an `iff` condition. The event must occur first and the guard is sampled when
that event arrives; changing the guard alone does not wake the process. The
timed slice admits scalar identifier, comparison, and logical guards on plain
`always` events and positive- or negative-edge `always_ff` clocks; the marker
remains explicit for unsupported expressions and guarded reset lists.

## Why the remaining conditional event controls stay loud

IEEE 1800-2023 §§9.2.2.4 and 9.4.2.3 make the guard part of event
registration, wake-up filtering and re-arming. The retained event-list
registration now carries a side-effect-free scalar guard and applies it at the
publication point. The retained evaluator covers identifiers, literals, scalar
equality/inequality comparisons, and logical `&&`/`||` combinations; calls,
selects and other general expressions still need a broader evaluator. `always_ff` guards
remain on the clock registration and preserve its inferred-clock and
single-driver rules. No second scheduler or guessed guard evaluation is
introduced.

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
