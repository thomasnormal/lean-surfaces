# Priority-if statements — repricing boundary

IEEE 1800-2023 §12.4.2 gives `priority if` listed-order evaluation and
first-true-branch selection. Later conditions are not selected after an
earlier true condition. When the chain has no true condition and no explicit
`else`, the construct reports a priority violation; an explicit `else`
handles the no-match case. The qualifier applies to the complete
`if`/`else-if` series, not to a later `else` arm.

## Why priority-if remains a boundary

The ordinary conditional envelope can preserve a first-match chain, but it has
no listed-order status or no-match diagnostic channel. Erasing the qualifier
would silently turn a required violation into ordinary fallthrough and would
make a chain without `else` equivalent to one with a fallback. A retained
process also needs the priority check to stay associated with its activation
when a selected body waits or an `always_comb` process is rescheduled.

The public tier therefore keeps every `ConditionalStatement:Priority` span
loud. It does not erase the qualifier, select a fixed branch, fabricate a
diagnostic, repair an invalid `priority` after `else`, or add a scheduler.

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
