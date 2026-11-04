# Pattern-condition boundary — retained matching and binding semantics

`ConditionalStatement:pattern` marks an `if` condition using SystemVerilog's
`matches` pattern operator. Constant patterns, identifier-binding patterns and
structure patterns with named members or `.*` wildcards remain explicit.

## Why pattern conditions remain loud

IEEE 1800-2023 §12.6 distinguishes integral constant matching, identifier
binding and structure-member matching. A binding pattern always succeeds while
assigning the matched value; named structure members are order-independent and
omitted members are ignored; `.*` matches any member without binding. The
legacy conditional evaluator has no pattern environment or aggregate member
layout. Treating every pattern as equality would lose bindings and wildcard
behavior. No second pattern evaluator is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `ConditionalStatement:pattern` in **12**
files: **5** are sole refusals and 7 co-occur. Re-elaborating the sole files
with the read-only repricer finds **9** pattern-condition spans:

| source shape | spans | files |
|---|---:|---:|
| constant integral pattern | 3 | 2 |
| identifier binding pattern | 2 | 1 |
| structure named-member pattern | 2 | 1 |
| structure wildcard pattern | 2 | 1 |
| structure-member pattern | 4 | 2 |

The member label overlaps the two structure forms. Reproduce the table with:

```text
python3.9 extractors/sv/pattern_condition_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument reports source shapes only; it does not bind pattern variables
or evaluate aggregate members.
