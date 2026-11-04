# Unique case statements — repricing boundary

IEEE §12.5.3 gives `unique case` a first-match selection plus a run-time
diagnostic when zero or multiple case items match. The diagnostic is separate
from the selected arm: a matching item still executes in source order. The
qualifier composes with `casez`, `casex`, `inside`, indexed subjects and
multi-label items.

## Why unique cases remain a boundary

The legacy envelope can lower an ordinary case to a first-match `If` chain,
but it has no diagnostic/status channel for unique violations and no retained
case-check state across a wait. Treating `unique` as ordinary `case` would
silently discard an observable error; choosing a fixed arm would change the
first-match rule. Wildcard and `inside` matching add their existing value
boundaries, while nonblocking arms still use the scheduler's publication path.

The public tier therefore keeps every `CaseStatement:Unique` span loud. No
diagnostic is fabricated, no qualifier is erased, and no second scheduler is
introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `CaseStatement:Unique` in **45** files:
**37** are unique-case-only and **8** co-occurring. Repricing the sole files
finds **38** spans: **20** have a `default` arm in **19** files, **9** use nonblocking updates,
**5** use indexed selects, **4** use multi-label items, **4** are `casez`, **1**
is `casex`, **1** uses `inside` and **1** has a nested block (features
overlap). Reproduce the table with:

```text
python3.9 extractors/sv/unique_case_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only and does not choose an arm or emit a diagnostic.
