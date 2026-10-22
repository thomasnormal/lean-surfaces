# Priority case statements — repricing boundary

IEEE 1800-2023 §12.5.3 gives `priority case` source-order, first-match
selection. A later item is not selected after an earlier match, even when
the item predicates overlap. When no item matches and there is no `default`,
the construct reports a priority violation; an explicit `default` supplies
the fallback. The qualifier composes with `casez` and `case inside`.

## Why priority cases remain a boundary

The ordinary case lowering can preserve a first-match chain and its selected
body, but it has no priority status or no-match diagnostic channel. Erasing
the qualifier would silently turn a required violation into normal fallthrough
and would make a source with no default appear equivalent to one with a
default. The envelope also has no retained priority-check state for a body
that waits or for a process that is rescheduled.

The public tier therefore keeps every `CaseStatement:Priority` span loud. It
does not erase the qualifier, select a fixed arm, fabricate a diagnostic, or
add a scheduler. Wildcard and `inside` operands retain their own value
boundaries, and nonblocking selected bodies retain the scheduler-owned
publication boundary.

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
