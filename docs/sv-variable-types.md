# Variable type boundary — retained aggregate storage diagnostics

`VariableSymbol:type` marks a variable declaration whose elaborated type is
outside the legacy variable store. The existing metadata-only array-query
rules can describe fixed dimensions, but they do not create runtime storage
for multidimensional unpacked arrays or packed/unpacked aggregate variables.
Frontend-invalid aggregate declarations remain diagnostic nodes.

## Why the type remains loud

IEEE 1800-2023 §§6.7.1, 7 and 20.7 distinguish packed element layout from
unpacked storage and number dimensions from slowest to fastest varying. A
scalar vector cannot stand in for a multidimensional variable: it would lose
element addressing, initialization and assignment state. The envelope also has
no recovery status for an unpacked struct or union with an illegal packed
dimension. No aggregate store, flattening shortcut or diagnostic recovery path
is introduced, and no second evaluator or scheduler is added.

## 2026-10-22 census and decision

The fresh 22,043-path census records `VariableSymbol:type` in **150** files;
**10** are sole refusals and 140 co-occur. The independent read-only repricer
finds **10** unsupported variable spans:

| source shape | spans | files |
|---|---:|---:|
| fixed unpacked-array storage | 9 | 9 |
| multidimensional unpacked storage | 7 | 7 |
| packed element type plus unpacked storage | 9 | 9 |
| invalid packed dimension on aggregate | 1 | 1 |

The array labels overlap. Reproduce the table with:

```text
python3.9 extractors/sv/variable_type_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it verifies the sole marker and reports source
shapes without allocating aggregate storage or repairing the invalid type.
