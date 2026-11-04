# Invalid hierarchy boundary — retained frontend diagnostics

`Hierarchy:invalid-compilation` marks a design whose module hierarchy could
not be elaborated because the frontend rejected a module instantiation or a
hierarchy-sensitive type use. The envelope retains one explicit unsupported
marker rather than executing a partially elaborated design.

## Why invalid hierarchies remain loud

IEEE 1800-2023 §§6.20.2, 6.20.4, 6.23, 23.3.2 and 23.10.2 constrain module
instance parameter assignment, empty port lists, localparam overrides and
hierarchical references inside `type()`. These checks happen during
elaboration and determine whether a complete instance tree exists. The legacy
envelope has no diagnostic stream or partial-hierarchy state from which to
recover a valid prefix. Dropping the marker would either invent an instance
or run a design that the source frontend rejected.

No second elaborator or hierarchy builder is introduced. Valid module
hierarchies retain their existing representation; only rejected designs stay
explicitly unsupported.

## 2026-10-22 census and decision

The fresh 22,043-path census records `Hierarchy:invalid-compilation` in **329**
files: **7** are sole refusals and 322 co-occur. Re-elaborating those sole
files with the read-only repricer finds **7** rejected hierarchy spans:

| source shape | spans | files |
|---|---:|---:|
| localparam override | 2 | 2 |
| mixed ordered and named parameters | 1 | 1 |
| duplicate named parameter | 1 | 1 |
| missing module-instance port list | 1 | 1 |
| port list on zero-port module | 1 | 1 |
| hierarchical `type()` reference | 1 | 1 |

Reproduce the table with:

```text
python3.9 extractors/sv/hierarchy_invalid_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument re-elaborates source in memory and writes no output beside the
read-only corpus. Its shape counts are telemetry, not an elaboration fallback.
