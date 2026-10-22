# Unique0 case statements — repricing boundary

IEEE 1800-2023 §12.5.3 gives `unique0 case` first-match selection and a
violation report when more than one case item expression matches. Unlike
`unique case`, no match is permitted and does not report a violation. The
qualifier composes with `casez`, `casex` and `case inside`.

## Why unique0 cases remain a boundary

The ordinary case lowering can preserve a first-match chain, but it has no
all-item overlap check or unique0 status distinguishing an allowed no-match
from a unique-case violation. Erasing the qualifier would silently discard a
multiple-match diagnostic; treating it like `unique` would fabricate a
no-match violation that IEEE explicitly excludes.

The public tier therefore keeps every `CaseStatement:Unique0` span loud. It
does not erase the qualifier, select a fixed arm, invent diagnostic text, or
add a case scheduler. Wildcard and `inside` operands retain their own value
boundaries.

## 2026-10-22 census and decision

The fresh 22,044-path census records `CaseStatement:Unique0` in **8** files,
all unique0-case-only. Repricing finds **10** spans:

| source shape | spans | files |
|---|---:|---:|
| first-match unique0 case | 10 | 8 |
| no-match allowed | 10 | 8 |
| no `default` fallback | 10 | 8 |
| no-match without violation row | 9 | 7 |
| `casex` | 3 | 2 |
| wildcard label | 4 | 3 |
| `case inside` | 2 | 1 |
| indexed select | 2 | 1 |
| `casez` | 1 | 1 |
| multiple-match violation row | 1 | 1 |

Rows overlap. Reproduce the measurement with:

```text
python3.9 extractors/sv/unique0_case_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only and never evaluates items, selects a branch,
reports a violation, or treats an allowed no-match as an error.
