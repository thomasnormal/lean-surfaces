# `supply0` net boundary — retained supply-strength driving

The legacy self-check tier admits an un-driven `supply0` declaration as a
declaration-initialized zero cell. A supply net with any continuous driver
remains at this boundary because the flat state has no strength lattice.

`NetSymbol:Supply0` marks a supply-strength net that continuously drives logic
zero. Its value participates in net resolution and dominates weaker drivers;
it is not an ordinary variable default.

## Why driven `supply0` remains loud

IEEE 1800-2023 §§6.6.6, 6.7.1, 10.3.4 and 28.15.3 give `supply0` a permanent
supply-strength driver. Replacing it with a literal zero loses strength and
driver identity when other sources connect. The envelope has no strength
lattice or supply driver set, so only the un-driven subset is rewritten; no
second scheduler or resolver is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `NetSymbol:Supply0` in **48** files: **5**
are sole refusals and 43 co-occur. Re-elaborating the sole files finds five
unsupported supply-net spans, all supply-strength drivers. Reproduce with:

```text
python3.9 extractors/sv/supply0_reprice.py --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only telemetry and does not resolve strength or create
a constant.
