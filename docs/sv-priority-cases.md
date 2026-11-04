# Priority case statements — admitted fallback boundary

IEEE 1800-2023 §12.5.3 gives `priority case` source-order, first-match
selection. A later item is not selected after an earlier match, even when
the item predicates overlap. When no item matches and there is no `default`,
the construct reports a priority violation; an explicit `default` supplies
the fallback. The qualifier composes with `casez` and `case inside`.

## The admitted fallback subset

The ordinary case lowering preserves a first-match chain and its selected body.
When a `priority case` has an explicit `default`, every no-match path is
covered, so the qualifier adds no observable diagnostic. The legacy self-check
tier lowers that subset, including the existing `casez` matching mode, after
the ordinary subject and pattern purity checks pass.

Cases without a fallback, dynamic or effectful subjects/patterns, unsupported
matching modes, and scheduler-facing bodies remain loud. No diagnostic state or
second scheduler is introduced.

`priority_case_fallback` supplies normal and `casez` differential PASS rows,
extractor regressions, and a Lean receipt.

## 2026-10-22 census and decision

The fresh 22,044-path census records `CaseStatement:Priority` in **12**
files, all priority-case-only. Repricing finds **13** spans:

| source shape | spans | files |
|---|---:|---:|
| first-match priority case | 13 | 12 |
| no `default` fallback | 6 | 6 |
| `default` fallback | 7 | 6 |
| indexed select | 5 | 4 |
| `casez` | 4 | 4 |
| wildcard label | 6 | 5 |
| `case inside` | 3 | 2 |
| multi-label item | 4 | 3 |
| `always_comb` context | 2 | 2 |
| explicit no-match violation row | 1 | 1 |

Rows overlap. Reproduce the measurement with:

```text
python3.9 extractors/sv/priority_case_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only and never evaluates case items, selects a branch,
or emits a violation report.
