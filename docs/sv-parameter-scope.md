# Compilation-unit parameter boundary — retained scope and shadowing

`ParameterSymbol` marks parameters declared in compilation-unit scope. They
are visible to later modules, may be referenced explicitly through `$unit::`,
and can be shadowed by a module parameter without changing the unit binding.

## Why compilation-unit parameters remain loud

IEEE 1800-2023 §§3.12.1 and 3.13 define a static compilation-unit scope and
explicit `$unit` lookup. The public envelope has no unit parameter store or
scope resolver. Copying a unit parameter into a module, resolving `$unit::U`
to a shadowing module parameter, or evaluating a default before source-order
visibility is established changes elaboration. No second scope builder is
introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `ParameterSymbol` in **25** files: **5**
are sole refusals and 20 co-occur. Re-elaborating the sole files finds **5**
unit-parameter spans: all are compilation-unit declarations; four source files
also exercise explicit `$unit::` references or module-parameter context. Reproduce with:

```text
python3.9 extractors/sv/parameter_scope_reprice.py --corpus /path/to/sv-tests-2/tests
```

The instrument reports scope shapes only and does not resolve parameter values.
