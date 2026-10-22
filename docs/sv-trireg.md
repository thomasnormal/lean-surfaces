# `trireg` charge-storage nets — repricing boundary

The legacy envelope admits ordinary four-state values and a limited set of
resolved net declarations, but it does not represent the charge-storage state
of a `trireg`. A `trireg` is driven while one or more drivers contribute a
non-`z` value; when all drivers float, it can retain the last resolved value in
a capacitive state. Its charge strength (`small`, `medium`, or `large`) and
optional decay delay affect that state, and connected capacitive nets can
propagate the strongest charge.

## Why `TriReg` remains a boundary

Treating a `trireg` as an ordinary `wire` would turn a release into `z` and
lose the stored charge. Treating it as a variable would lose continuous
driver resolution, four-state `x` propagation, multiple-driver behavior and
the distinction between driven and capacitive states. A declaration delay on
the charge storage also needs a timed decay publication, which is distinct
from the existing net and continuous-assignment delay boundaries. The current
envelope has none of this per-net driver, charge or decay state, so no
`TriReg` declaration is admitted and no second scheduler is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `NetSymbol:TriReg` in **53** files:
**17** are `TriReg`-only and **36** co-occur with another wall. The read-only
repricer finds **21** concrete declarations in the 17 sole files:

| source shape | declarations | files |
|---|---:|---:|
| explicit charge strength | 11 | 7 |
| driver release / high-impedance transition | 14 | 11 |
| capacitive or retained-charge observation | 9 | 6 |
| four-state `x` drive or check | 4 | 3 |
| undriven startup observation | 2 | 2 |
| charge-strength network | 2 | 1 |
| charge-decay delay | 1 | 1 |
| signed packed vector | 1 | 1 |

Rows overlap because one declaration can have a strength, a release and a
four-state observation. Reproduce the measurement with:

```text
python3.9 extractors/sv/trireg_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument reads each source in process and writes no envelope beside the
corpus. Its shape counts are telemetry for a future driver and charge-state
representation, not an implementation of `trireg` semantics.
