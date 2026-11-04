# Random sequence productions — repricing boundary

`randsequence` defines a production graph whose next production is selected
by constrained randomization. Alternatives, weighted productions, conditional
and case productions, repeats, recursion and action blocks all affect the
generated sequence. Action blocks execute in an automatic production scope and
can update design state. The statement is therefore both a random source and
a procedural expansion boundary.

## Why random sequence remains a boundary

The public envelope has no constrained-random engine, random-sequence
production graph, random-state oracle or generated action frame. It cannot
select a weighted alternative reproducibly, retain recursive production state,
or execute each action with the required automatic scope. Returning one branch,
using a fixed seed or flattening the productions would fabricate observable
behavior. Actions can also contain waits and assignments whose continuations
must call the existing scheduler.

The tier keeps every `RandSequenceStatement` loud until an explicit random
oracle and production/action representation exist. No deterministic branch,
source-order shortcut or second scheduler is introduced.

## 2026-10-21 census and decision

The fresh 22,043-path census records `RandSequenceStatement` in **72** files:
**53** are randsequence-only and **19** co-occur with another wall. The sole
files contain **54** production blocks. Their source spans include overlapping
features:

| production feature | instances | files |
|---|---:|---:|
| action blocks | 54 | 53 |
| alternatives (`|`) | 18 | 17 |
| conditional/case productions | 15 | 15 |
| repeats | 10 | 10 |
| weighted choices (`:=`) | 10 | 9 |

These labels are frontend-span telemetry, not an admission claim. No feature
is independently admissible. Reproduce the table with:

```text
python3.9 extractors/sv/randsequence_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument reads each source in process and writes no envelope beside the
corpus. Its feature counts are telemetry for the randomization boundary, not a
random sequence evaluator.
