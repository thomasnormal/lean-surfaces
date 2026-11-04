# Case-subject boundary — retained subject evaluation

`CaseStatement:subject` marks a case statement whose subject expression is
outside the legacy case lowering. The ordinary case chain has a pure integral
subject and existing first-match rules; time reads, elaboration constants,
packed aggregate members and selected fields need distinct source evaluation
and type/layout state.

## Why these subjects remain loud

IEEE 1800-2023 §§11.4, 12.5 and 20 require subject sizing/evaluation before
case-item matching. `$time` is scheduler-visible, aggregate members use packed
layout and aliasing, and frontend-bound constants may be elaboration-only. The
legacy envelope has no general subject plan for these contexts. No subject is
replaced with a stale literal, no aggregate is flattened and no second
evaluator or scheduler is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `CaseStatement:subject` in **30** files;
**8** are sole refusals and 22 co-occur. The independent read-only repricer
finds **8** unsupported case spans:

| source shape | spans | files |
|---|---:|---:|
| `$time` subject | 5 | 5 |
| constant-expression subject | 1 | 1 |
| packed-union member subject | 1 | 1 |
| packed-struct part-select subject | 1 | 1 |

Reproduce the table with:

```text
python3.9 extractors/sv/case_subject_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it verifies the sole marker and reports source
shapes without evaluating time, rebuilding elaboration constants or resolving
aggregate layout.
