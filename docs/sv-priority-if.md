# Priority-if statements — repricing boundary

IEEE 1800-2023 §12.4.2 gives `priority if` listed-order evaluation and
first-true-branch selection. Later conditions are not selected after an
earlier true condition. When the chain has no true condition and no explicit
`else`, the construct reports a priority violation; an explicit `else`
handles the no-match case. The qualifier applies to the complete
`if`/`else-if` series, not to a later `else` arm.

## The admitted fallback subset

The ordinary conditional envelope preserves listed-order, first-match
selection. A `priority if` chain with an explicit final `else` has no possible
no-match diagnostic, so the legacy self-check tier lowers that subset to an
ordinary `If`. Indexed and dynamic conditions, missing fallbacks, invalid
qualifier placement, and scheduler-facing forms remain loud because their
priority behavior is still observable.

The public tier does not select a fixed branch, fabricate a diagnostic, or add a
scheduler.

## 2026-10-22 census and decision

The fresh 22,044-path census records `ConditionalStatement:Priority` in **9**
files, all priority-if-only. Repricing finds **9** spans:

| source shape | spans | files |
|---|---:|---:|
| first-match/listed-order priority-if | 9 | 9 |
| condition chain | 8 | 8 |
| explicit `else` fallback | 6 | 6 |
| no-match path without final `else` | 2 | 2 |
| potentially multiple-true conditions | 4 | 4 |
| indexed select | 2 | 2 |
| `always_comb` context | 2 | 2 |
| explicit no-match violation row | 1 | 1 |
| invalid `priority` after `else` | 1 | 1 |

Rows overlap. Reproduce the measurement with:

```text
python3.9 extractors/sv/priority_if_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only and never evaluates a condition, selects a
branch, or emits a violation report.
