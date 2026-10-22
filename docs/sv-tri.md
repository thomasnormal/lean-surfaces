# `tri` resolved nets — repricing boundary

The `tri` net type is the resolved-wire spelling in IEEE 1800-2023 §6.6.1.
With one driver it takes that driver's value, and with several drivers it
resolves their four-state values according to net-driver strengths. Its
undriven value is high impedance. `wire` and `tri` are equivalent names for
the same resolved-net behavior; `tri reg` remains an invalid declaration.

## Why `Tri` remains a boundary

The legacy envelope has a flat value store and can carry a narrow continuous
driver, but it has no general driver set or strength-resolution state. A
single-driver `tri` can look like a plain wire, yet that rewrite changes the
meaning when another driver is added and hides the high-impedance floating
state. The invalid spelling also belongs to frontend diagnostics rather than
runtime storage. No `tri` declaration is admitted by renaming it, and no
second scheduler or recovery elaborator is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `NetSymbol:Tri` in **66** files: **7**
are `Tri`-only and **59** co-occur with another wall. The read-only repricer
finds **7** concrete declarations in the sole files:

| source shape | declarations | files |
|---|---:|---:|
| resolved `tri` declaration | 7 | 7 |
| continuous single driver | 3 | 3 |
| undriven observation | 4 | 4 |
| `wire`/`tri` equivalence comparison | 2 | 2 |
| invalid `tri reg` spelling | 2 | 2 |
| floating four-state observation | 1 | 1 |

Rows overlap. Reproduce the measurement with:

```text
python3.9 extractors/sv/tri_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument reports source shapes only; it does not resolve multiple
drivers or turn the invalid declaration into a partial runtime design.
