# `supply1` net boundary — retained supply-strength driving

The legacy self-check tier admits an un-driven `supply1` declaration as a
declaration-initialized one cell. A supply net with any continuous driver
remains at this boundary because the flat state has no strength lattice.

`NetSymbol:Supply1` marks a supply-strength net that continuously drives logic
one. Its value is not an ordinary variable default: the supply driver
participates in net resolution and dominates weaker drivers. Continuous
assignment strength rules explicitly preserve this exception.

## Why driven `supply1` remains loud

IEEE 1800-2023 §§6.6.6, 6.7.1, 10.3.4 and 28.15.3 give `supply1` a permanent
supply-strength driver. Replacing it with a literal one loses strength and
driver identity, changing resolution when other sources are connected. The
legacy envelope has no strength lattice or supply driver set. Only the
un-driven subset is rewritten as a constant, and no second scheduler or
resolver is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `NetSymbol:Supply1` in **56** files; **5**
are sole refusals and 51 co-occur. The independent read-only repricer finds
**5** unsupported supply-net spans:

| source shape | spans | files |
|---|---:|---:|
| supply-strength driver | 5 | 5 |
| logic-one source | 5 | 5 |
| continuous-strength context | 1 | 1 |

The labels overlap. Reproduce the table with:

```text
python3.9 extractors/sv/supply1_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it verifies the sole marker and reports source
shapes without resolving supply strength or fabricating a constant.
