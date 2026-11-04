# Hierarchy timescale boundary — retained time-unit scope

`Hierarchy:timescale` marks a design whose modules use distinct `timescale`
directives or module time declarations. Time units and precision are inherited
by source order and affect delays and time observations.

## Why timescale remains loud

IEEE 1800-2023 §§22.7, 37.2 and 38.13 require per-module time-unit scope,
precision rounding and inherited directive ordering. The public hierarchy has
no time-scale environment attached to each instance. Applying the top module's
scale globally or ignoring a child scale changes `#` delays and `$time` values.
No second time scheduler or global-scale shortcut is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `Hierarchy:timescale` in **27** files:
**5** are sole refusals and 22 co-occur. Re-elaborating the sole files finds
**5** timescale hierarchy spans, all with directive scope and time-observation
or delay uses. Reproduce with:

```text
python3.9 extractors/sv/timescale_reprice.py --corpus /path/to/sv-tests-2/tests
```

The instrument reports source shapes only and does not choose a global time
scale or advance simulation.
