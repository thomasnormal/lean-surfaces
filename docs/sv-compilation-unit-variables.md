# Compilation-unit variable boundary — retained `$unit` scope

`VariableSymbol` marks the residual variable boundary for declarations outside
modules and for declarations whose legal elaboration creates more than one
top-level hierarchy root. It is distinct from `VariableSymbol:type`, which
describes an unsupported variable type. The residual sole rows also include an
enumeration range declaration and an invalid packed dimension on `int`.

## Why these variables remain loud

IEEE 1800-2023 §§3.11–3.13 and 6.21 give compilation-unit variables static
lifetime, `$unit` name resolution and visibility across modules. Multiple
uninstantiated modules are separate top-level hierarchy blocks. The envelope
has one module root and no compilation-unit store or explicit `$unit` resolver;
the invalid aggregate and enum forms likewise need frontend declaration state.
No unit variable is copied into a module, no top-level module is silently
dropped, no enum range is reconstructed and no invalid integer declaration is
repaired. No second hierarchy builder, evaluator or scheduler is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `VariableSymbol` in **76** files; **10**
are sole refusals and 66 co-occur. The independent read-only repricer finds
**10** unsupported variable spans:

| source shape | spans | files |
|---|---:|---:|
| compilation-unit variable | 9 | 9 |
| multiple top-level modules | 2 | 2 |
| enum range declaration | 1 | 1 |
| invalid packed dimension on `int` | 1 | 1 |

The compilation-unit and multiple-top-level labels overlap. Reproduce the table
with:

```text
python3.9 extractors/sv/variable_symbol_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it verifies the sole marker and reports source
shapes without inventing a `$unit` store or hierarchy semantics.
