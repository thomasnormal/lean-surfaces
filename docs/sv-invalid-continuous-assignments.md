# Invalid continuous-assignment boundary — retained default-nettype diagnostics

`ContinuousAssignSymbol:InvalidExpression` marks a continuous assignment whose
expression cannot be elaborated under the active ``default_nettype`` rules.
The marker retains the rejected assignment instead of creating an implicit net
or executing a partial driver.

## Why these assignments remain loud

IEEE 1800-2023 §§22.5.3 and 22.8 make the active default net type a
source-order directive. `default_nettype none` rejects undeclared net uses;
`undefineall` removes text macros without resetting that directive, and
`supply0`/`supply1` are not valid `default_nettype` values. The public envelope
has no directive-state timeline or implicit-net diagnostic state. Inventing a
wire, treating `supply0` as a legal declaration, or resetting the directive
after `undefineall` would change elaboration and continuous-driver behavior.

No second preprocessor, net resolver or recovery evaluator is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `ContinuousAssignSymbol:InvalidExpression`
in **14** files: **6** are sole refusals and 8 co-occur. Re-elaborating those
sole files with the read-only repricer finds **7** rejected assignment spans:

| source shape | spans | files |
|---|---:|---:|
| `default_nettype none` implicit-net rejection | 5 | 4 |
| invalid `default_nettype supply0/supply1` | 2 | 2 |

The labels overlap for the `undefineall` row. Reproduce the table with:

```text
python3.9 extractors/sv/continuous_invalid_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument re-elaborates source in memory and writes no output beside the
read-only corpus. Its shape counts are telemetry, not implicit-net recovery.
