# Concurrent assertions — repricing boundary

Concurrent assertions remain explicit `ConcurrentAssertionStatement`
refusals. The existing immediate assertion contract handles a condition and
an action in the current procedural step; it does not provide a concurrent
property engine or sampled-value history.

## Why concurrent assertions remain a boundary

An SVA property samples signals in Preponed at a clock or event, creates one
or more active attempts, advances sequence match state over later ticks, and
evaluates the result in Observed. Pass/fail or coverage actions then publish
through the appropriate Reactive/coverage path. `disable iff`, vacuity,
`first_match`, unbounded ranges, `accept_on`/`reject_on`, and local variables
all retain state across scheduler steps. A no-clock property still needs the
assertion engine's attempt and sampled-value rules.

The statement flavors are not interchangeable: `assert`, `assume`, `cover`,
`expect`, and `restrict` differ in failure, coverage, blocking and formal
meaning. Treating a property as an immediate boolean, evaluating it in Active,
or dropping its action would fabricate observable behavior. The public tier
therefore keeps these forms loud and does not add a second scheduler or an
ad-hoc assertion engine.

## 2026-10-21 census and decision

The fresh 22,043-path census records `ConcurrentAssertionStatement` in **1,358**
files: **539** are assertion-only and **819** co-occur with another wall. The
repricer finds **639** unsupported statement instances in the 539 sole files:

| statement flavor | instances | files |
|---|---:|---:|
| `assert property` | 562 | 491 |
| `cover property` | 37 | 37 |
| `assume property` | 9 | 9 |
| `cover sequence` | 8 | 8 |
| `expect` | 21 | 19 |
| `restrict` / `restrict property` | 2 | 2 |

The file column overlaps when one source contains several flavors. Every row
requires sampled values, attempt state and scheduler-region publication; no
flavor is an independently admissible immediate assertion. Existing immediate
assertion actions remain the acceptance boundary. Reproduce the table with:

```text
python3.9 extractors/sv/concurrent_assert_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument reads each source in process and writes no envelope beside the
corpus. Its statement-shape counts are telemetry, not a property evaluator.
