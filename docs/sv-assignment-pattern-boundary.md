# Assignment-pattern boundary — retained typed aggregate shape

`AssignmentPattern:integral-shape` marks a typed assignment-pattern expression
whose self-determined packed shape is outside the admitted integral pattern
metadata. The pattern remains explicit; its fields are not flattened into a
guessed vector.

## Why these patterns remain loud

IEEE 1800-2023 §10.9 gives a typed assignment pattern its own data type and
packs each element according to the declared dimensions before an enclosing
expression or cast sees the value. The legacy envelope has no general typed
aggregate layout or self-determined pattern value. Treating `T'{1,2}` as an
untyped concatenation changes dimension order and width, especially when
patterns are nested inside a concatenation and then cast to `shortint`.

No second aggregate evaluator is introduced. Existing scalar and admitted
one-dimensional integral patterns retain their current behavior; these
multi-dimensional typed forms remain loud.

## 2026-10-22 census and decision

The fresh 22,043-path census records `AssignmentPattern:integral-shape` in
**5** files, all **5** sole refusals. Re-elaborating those rows with the
read-only repricer finds **10** unsupported pattern spans:

| source shape | spans | files |
|---|---:|---:|
| typed packed pattern | 10 | 5 |
| casted pattern expression | 10 | 5 |
| nested pattern in concatenation | 10 | 5 |

The labels overlap. Reproduce the table with:

```text
python3.9 extractors/sv/assignment_pattern_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only telemetry: it re-elaborates source in memory and
does not construct a packed aggregate value.
