# Elaboration system-task boundary — retained severity effects

`ElabSystemTaskSymbol:ElabSystemTask` marks `$info` and `$warning` calls made
while elaborating a generate or module item. They produce diagnostics before
simulation and do not themselves prevent a valid design from starting.

## Why elaboration tasks remain loud

IEEE 1800-2023 §20.10.1 gives elaboration severity tasks source location and
hierarchical-scope obligations distinct from runtime system tasks. The public
envelope has no elaboration diagnostic stream or pre-simulation output phase.
Treating these calls as runtime `$display`, dropping them, or making `$warning`
fatal changes diagnostics and simulation admission. No second elaborator or
output scheduler is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `ElabSystemTaskSymbol:ElabSystemTask` in
**12** files: **5** are sole refusals and 7 co-occur. Re-elaborating the sole
files with the read-only repricer finds **6** elaboration-task spans:

| source shape | spans | files |
|---|---:|---:|
| `$info` | 5 | 4 |
| `$warning` | 3 | 2 |

The labels overlap where one file contains both. Reproduce the table with:

```text
python3.9 extractors/sv/elab_task_reprice.py --corpus /path/to/sv-tests-2/tests
```

The instrument reports syntax only; it does not emit diagnostics or alter
simulation admission.
