# Unique0 case statements

IEEE 1800-2023 §12.5.3 gives `unique0 case` first-match selection and a
violation report when more than one case item expression matches. Unlike
`unique case`, no match is permitted and does not report a violation. The
qualifier composes with `casez`, `casex` and `case inside`.

## Admitted subset

The legacy self-check tier lowers an ordinary `unique0 case` when every label
is an integral literal and labels are distinct after whole-case sizing. The
ordinary first-match chain preserves matching and the allowed no-match path;
an explicit `default` is optional. This admits no overlap-diagnostic state and
does not add a scheduler.

The following remain loud: wildcard and `inside` matching, duplicate labels,
dynamic or non-integral labels, effectful subjects or patterns,
scheduler-facing bodies, and any other unsupported case expression. The
qualifier is not erased for those forms, and no diagnostic text is invented.

## 2026-10-22 census and decision

The committed 22,044-path census records `CaseStatement:Unique0` in **8**
files, all unique0-case-only. Repricing finds **10** spans:

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

The admitted fixture `Examples/system-verilog/unique0_case` exercises both a
matching label and an allowed no-match path. Rows overlap. Reproduce the
source-shape measurement with:

```text
python3.9 extractors/sv/unique0_case_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only and never evaluates items, selects a branch,
reports a violation, or treats an allowed no-match as an error.
