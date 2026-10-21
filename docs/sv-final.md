# Final procedures — repricing boundary

`ProceduralBlockSymbol:Final` marks an IEEE final procedure. A final
procedure runs once when simulation ends, after the finish condition and
before the simulator's final callbacks. It executes in a function-like
shutdown context rather than as an ordinary concurrent process.

## Why final procedures remain a boundary

Final execution observes the last settled design state, including relevant
NBA work, and has ordering and completion rules distinct from `initial` and
`always`. It cannot be delayed or treated as an independent process; `$finish`
inside it ends the shutdown immediately. The current envelope has no
end-of-simulation queue, final invocation context or completion phase.

The public tier therefore keeps every final procedure loud. It does not run a
final body at time zero, ignore a delay/wait, or append a second shutdown
scheduler. The existing core's completion rules remain the dependency for any
future final lowering.

## 2026-10-21 census and decision

The fresh 22,043-path census records `ProceduralBlockSymbol:Final` in **88**
files: **39** are final-only and **49** co-occur with another wall. The sole
files contain **45** final spans. Their source features overlap:

| source feature | instances | files |
|---|---:|---:|
| block bodies (`final begin`) | 39 | 38 |
| assignments/increments | 33 | 29 |
| `$display` | 38 | 36 |
| `$finish` | 4 | 4 |
| assertions/`$fatal` | 2 | 2 |
| delays | 3 | 3 |
| `wait` | 1 | 1 |
| `$time` | 1 | 1 |

These labels describe recovered spans, not an admission claim. Reproduce the
table with:

```text
python3.9 extractors/sv/final_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only and does not execute shutdown code.
