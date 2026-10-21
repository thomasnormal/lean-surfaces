# Covergroup declarations — repricing boundary

`CovergroupType:CovergroupType` marks a covergroup declaration. Covergroups
sample values into bins and crosses, optionally on a clock or through an
explicit sample method. They are verification objects with their own
coverage state, not ordinary module declarations or procedural blocks.

## Why covergroup declarations remain a boundary

The current envelope has no covergroup object, sampling event, bin database,
cross product or coverage query state. An `option` assignment changes the
coverage model, and `with` expressions are evaluated in the coverpoint's
sample context. Flattening a covergroup into a scalar declaration would lose
that state and could change when a sample is counted. Sampling also calls the
existing scheduler's event rules when a clock or explicit sample method is
present.

The public tier therefore keeps every covergroup declaration explicit. It
does not choose bins, run a fixed sampling schedule, or add a second
scheduler. Coverpoint and cross shapes remain loud until a typed coverage
object model is available.

## 2026-10-21 census and decision

The fresh 22,043-path census records `CovergroupType:CovergroupType` in **725**
files: **8** are covergroup-only and **717** co-occur with another wall. The
sole files contain **9** unsupported covergroup spans. Their source features
overlap:

| source feature | instances | files |
|---|---:|---:|
| coverpoints | 9 | 8 |
| bins | 6 | 5 |
| clocked sampling | 3 | 2 |
| sample-argument directions | 3 | 3 |
| options | 2 | 2 |
| sample methods | 2 | 2 |
| `with` expressions | 1 | 1 |
| crosses | 1 | 1 |

These labels describe recovered source spans, not an admission claim.
Reproduce the table with:

```text
python3.9 extractors/sv/covergroup_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only and does not execute coverage sampling.
