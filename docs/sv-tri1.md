# `tri1` implicit pull nets — repricing boundary

The legacy self-check tier admits an un-driven `tri1` declaration as a
declaration-initialized one cell. A pull net with any continuous driver
remains at the existing strength-resolution boundary.

The legacy envelope admits an ordinary four-state `wire` with a limited
procedural store, but it does not represent the implicit driver attached to a
`tri1` net. IEEE 1800-2023 §§6.6.5 and 28.15.1 give an undriven `tri1` a
logic-1 value with pull strength. An explicit driver is resolved against that
pull driver: a sufficiently strong source overrides it, while an unknown
source remains an unknown resolved value.

## Why driven `Tri1` remains a boundary

Replacing `tri1` with a constant one loses the live driver relationship and
changes the result as soon as a continuous source drives or releases the net.
Replacing it with a plain `wire` loses the implicit pull and its strength
ordering. The current envelope has no per-net driver set, strength lattice or
four-state resolution state. Only the un-driven pull value is represented;
driven forms remain loud, and no second scheduler is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `NetSymbol:Tri1` in **20** files: **10**
are `Tri1`-only and **10** co-occur with another wall. The read-only repricer
finds **10** concrete declarations in the sole files:

| source shape | declarations | files |
|---|---:|---:|
| implicit pull-1 declaration | 10 | 10 |
| undriven observation | 6 | 6 |
| continuous driver | 4 | 4 |
| strong driver overriding pull-1 | 3 | 3 |
| driver release / high impedance | 1 | 1 |
| four-state `x` driver | 1 | 1 |

Rows overlap. Reproduce the measurement with:

```text
python3.9 extractors/sv/tri1_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument only reports source shapes; it does not resolve a driver,
choose a strength or lower a `tri1` to a constant.
