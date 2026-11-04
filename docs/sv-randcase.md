# Randcase statements — repricing boundary

IEEE §12.10 and §18.16 define `randcase` as a weighted random branch
selection. Each weight expression is sampled for the execution, zero-weight
branches are excluded, and an all-zero total has its own diagnostic behavior.
The selected statement then executes with ordinary procedural effects.

## Why randcase remains a boundary

The current envelope has no random oracle, sampled weight vector or weighted
selection trace. Choosing the first positive branch, using a fixed seed, or
discarding a zero-weight diagnostic would fabricate a result. Branches can
contain blocking, nonblocking, indexed and compound effects that must retain
their existing scheduler semantics.

The public tier therefore keeps every `RandCaseStatement` loud. No branch is
chosen, no random state is invented, and no second scheduler is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `RandCaseStatement` in **35** files:
**31** are randcase-only and **4** co-occurring. Repricing the sole files
finds **33** spans: **3** all-zero-weight cases, **12** with a zero-weight
branch, **10** expression-weight spans, **7** indexed targets, **21** increments
and **1** branch block (features overlap). Reproduce the table with:

```text
python3.9 extractors/sv/randcase_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only and never selects a weighted branch.
