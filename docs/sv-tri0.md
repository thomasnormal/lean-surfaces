# `tri0` implicit pull nets — repricing boundary

The legacy self-check tier admits an un-driven `tri0` declaration as a
declaration-initialized zero cell. A pull net with any continuous driver
remains at the existing strength-resolution boundary.

The legacy envelope admits an ordinary four-state `wire` with a limited
procedural store, but it does not represent the implicit driver attached to a
`tri0` net. IEEE 1800-2023 §§6.6.5 and 28.15.1 give an undriven `tri0` a
logic-0 value with pull strength. An explicit driver is resolved against that
pull driver: a sufficiently strong source overrides it, while an unknown
source remains an unknown resolved value.

## Why driven `Tri0` remains a boundary

Replacing `tri0` with a constant zero loses the live driver relationship and
changes the result as soon as a continuous source drives or releases the net.
Replacing it with a plain `wire` loses the implicit pull and its strength
ordering. The current envelope has no per-net driver set, strength lattice or
four-state resolution state. Only the un-driven pull value is represented;
driven forms remain loud, and no second scheduler is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `NetSymbol:Tri0` in **22** files: **11**
are `Tri0`-only and **11** co-occur with another wall. The read-only repricer
finds **11** concrete declarations in the sole files:

| source shape | declarations | files |
|---|---:|---:|
| implicit pull-0 declaration | 11 | 11 |
| undriven observation | 8 | 8 |
| continuous driver | 3 | 3 |
| explicit driver strength | 1 | 1 |
| strong driver overriding pull-0 | 1 | 1 |
| four-state `x` driver | 1 | 1 |

Rows overlap. Reproduce the measurement with:

```text
python3.9 extractors/sv/net_pull_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument only reports source shapes; it does not resolve a driver,
choose a strength or lower a `tri0` to a constant.
