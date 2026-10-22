# Invalid static-local boundary — retained frontend diagnostics

`StaticLocal:invalid-compilation` is the frontend recovery marker for a
procedural block whose local declaration or block syntax is illegal. It also
covers lexical errors that prevent the block from forming a valid static-local
frame. The marker remains explicit; no partially parsed local is executed.

## Why invalid static locals remain loud

IEEE 1800-2023 §§5.5, 5.7.1, 6.21 and 9.3.5 constrain comment/token grammar,
declaration order and block-label syntax. These checks happen before a local
store exists. The envelope has no diagnostic stream or recovery frame from
which to infer whether a malformed declaration was intended to be visible,
whether a label names the block or a statement, or whether a number token is
valid. No parser recovery shortcut or second local-store evaluator is
introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `StaticLocal:invalid-compilation` in **241**
files: **7** are sole refusals and 234 co-occur. Re-elaborating those sole
files with the read-only repricer finds **7** rejected static-local spans:

| source shape | spans | files |
|---|---:|---:|
| nested block comment | 1 | 1 |
| embedded space in number | 1 | 1 |
| sign between number base and digits | 1 | 1 |
| declaration after statement | 1 | 1 |
| declaration after use | 1 | 1 |
| label and block name | 1 | 1 |
| label before block-end keyword | 1 | 1 |

Reproduce the table with:

```text
python3.9 extractors/sv/static_invalid_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument re-elaborates source in memory and writes no output beside the
read-only corpus. Its shape counts are telemetry, not parser recovery.
