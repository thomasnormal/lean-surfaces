# `always_latch` — inferred-sensitivity boundary

IEEE 1800-2023 §9.2.2.3 defines `always_latch` as an automatically activated
procedural block with the inferred-sensitivity rules of `always_comb` and
latch behavior: assignments may update outputs when enables are active, while
unassigned outputs retain their previous values. Its time-zero activation,
retriggering on every inferred input change, and restriction against timing
controls and fork/join are process semantics.

The legacy envelope has separate `AlwaysComb` and clocked-process forms, but
no inferred sensitivity set, latch-hold state, or process-kind diagnostics.
Rewriting `always_latch` as `always_comb` loses retention; rewriting it as a
plain `always` loses automatic activation and sensitivity. The tier therefore
keeps `ProceduralBlockSymbol:AlwaysLatch` loud and introduces no sensitivity
guesser or second scheduler.

## 2026-10-22 census and decision

The fresh 22,043-path census records `ProceduralBlockSymbol:AlwaysLatch` in
**53** files; **13** are always-latch-only and 40 co-occur. The independent
read-only repricer finds 13 latch spans in the sole files. Features overlap:

| feature | spans | files |
|---|---:|---:|
| inferred sensitivity | 12 | 12 |
| nonblocking assignment | 6 | 6 |
| mixed or timed companion processes | 2 | 2 |
| explicit timing-control diagnostic | 1 | 1 |
| forbidden fork/join diagnostic | 1 | 1 |
| multiple outputs | 1 | 1 |
| nested enables | 1 | 1 |
| protected lexical region | 1 | 1 |

Reproduce the table with:

```text
python3.9 extractors/sv/always_latch_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it verifies the sole marker and reports source
features without registering inferred waits, retaining latch state, or
changing process admission.
