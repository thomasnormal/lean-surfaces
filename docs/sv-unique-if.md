# Unique-if statements — repricing boundary

IEEE 1800-2023 §12.4.2 gives `unique if` ordinary first-true-branch
selection while requiring every named condition to be checked for overlap.
More than one true condition reports a violation after the current procedural
evaluation, while the first true branch still executes. A chain without an
explicit `else` reports a no-match violation when every condition is false;
an explicit `else` covers that case.

Section 12.4.2.1 adds process interaction: checks can be deferred to the
Observed region, pending reports are discarded when a process resumes from an
event control, and an `always_comb` reschedule flushes reports from transient
active-region evaluation. A loop can create one check per iteration, tied to
the same retained process activation.

## The admitted fallback subset

The legacy envelope can represent an ordinary `if` chain, but it has no
uniqueness status or diagnostic channel. A `unique if` chain is therefore
admitted only when every condition is a distinct literal equality over one
integral variable and an explicit final `else` covers no-match. Those
conditions cannot overlap, and the fallback removes the no-match diagnostic, so
the chain lowers soundly to an ordinary first-match `If`. Dynamic conditions,
possibly overlapping values, missing fallbacks, Observed-region behavior, and
invalid qualifier placement remain loud. No diagnostic text or scheduler is
invented.

## 2026-10-22 census and decision

The fresh 22,044-path census records `ConditionalStatement:Unique` in **20**
files: **16** are unique-if-only and **4** co-occur with another wall.
Repricing the sole files finds **16** spans:

| source shape | spans | files |
|---|---:|---:|
| first-match unique-if | 16 | 16 |
| condition chain | 15 | 15 |
| no-match path without final `else` | 10 | 10 |
| explicit `else` fallback | 6 | 6 |
| potentially multiple true conditions | 4 | 4 |
| `always_comb` context | 3 | 3 |
| reschedule flush | 2 | 2 |
| nested unique-if chain | 1 | 1 |
| ordinary `always` context | 1 | 1 |
| Observed-region report | 1 | 1 |
| event-control resume flush | 1 | 1 |
| loop context | 1 | 1 |
| invalid `unique` after `else` | 1 | 1 |

Rows overlap. Reproduce the measurement with:

```text
python3.9 extractors/sv/unique_if_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only and never evaluates a condition, reports a
diagnostic, flushes a pending report, or selects a branch.
