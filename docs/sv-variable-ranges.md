# Variable packed-range boundary — retained multidimensional range metadata

`VariableSymbol:range` marks a variable whose packed range geometry is outside
the legacy variable representation. One-dimensional packed scalar ranges and
the previously admitted fixed metadata-query slice remain available; this
boundary covers multidimensional packed ranges, including packed arrays of
packed-struct elements.

## Why these ranges remain loud

IEEE 1800-2023 §§6.4, 7.2 and 20.6–20.7 preserve packed dimension order,
singular integral value identity and width products across nested ranges. The
legacy envelope has no complete multidimensional range descriptor for these
variables. Flattening dimensions or treating a packed struct array as an
unpacked store would change `$bits`, `$size`, slicing and aggregate identity.
No range is collapsed, no width is guessed and no second evaluator or
scheduler is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `VariableSymbol:range` in **62** files;
**7** are sole refusals and 55 co-occur. The independent read-only repricer
finds **7** unsupported range spans:

| source shape | spans | files |
|---|---:|---:|
| multidimensional packed range | 4 | 4 |
| packed-struct array range | 3 | 3 |

Reproduce the table with:

```text
python3.9 extractors/sv/variable_range_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it verifies the sole marker and reports source
shapes without flattening packed dimensions or allocating aggregate storage.
