# Conditional event (`iff`) boundary — retained wait qualification

`SignalEventControl:iff` marks an event control whose trigger is qualified by
an `iff` condition. The event must occur first and the guard is sampled when
that event arrives; changing the guard alone does not wake the process. The
timed slice admits scalar identifier guards on plain `always` events and
positive- or negative-edge `always_ff` clocks; the marker remains explicit for
compound guards and guarded reset lists.

## Why the remaining conditional event controls stay loud

IEEE 1800-2023 §§9.2.2.4 and 9.4.2.3 make the guard part of event
registration, wake-up filtering and re-arming. The retained event-list
registration now carries a scalar identifier guard and applies it at the
publication point. Compound expressions still need a general evaluator, and
`always_ff` guards are retained on the clock registration and preserve its
inferred-clock and single-driver rules. No second scheduler or guessed guard
evaluation is introduced.

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
