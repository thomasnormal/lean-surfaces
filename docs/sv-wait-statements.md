# Level-sensitive wait statements — repricing boundary

IEEE §9.4.3 and §12.6.3 define `wait (expression)` as a level-sensitive
control. The expression is sampled when the statement is reached; if it is
true, execution continues in the same time slot. Otherwise the process keeps
its continuation and re-evaluates the condition after relevant updates until
the result is true. A wait is not an edge control: an already-true condition
does not block, and a false-to-true transition releases the saved body at the
current scheduler point. Compound conditions retain their four-state
truthiness, and a trailing delay begins only after the wait releases.

## Why general wait statements remain a boundary

The public envelope has no level-wait condition sampler, inferred dependency
set, re-evaluation registration or retained continuation for a condition that
can change. It also has no representation for named-event `triggered` state,
same-time NBA publication, or the interaction between a wait and process
control. Reducing `wait (a && b)` to one operand, treating it as an edge wait,
or executing the body immediately would lose wake-up order and four-state
behavior. The tier therefore keeps `WaitStatement` loud and introduces no
second scheduler.

## 2026-10-22 census and decision

The fresh **22,035**-path census records `WaitStatement` in **65** files: **18**
are wait-only and **47** co-occur with another wall. The sole files contain
**18** wait spans. Their overlapping source shapes include already-true/no-
block cases, delayed false-to-true releases, conjunction and disjunction
conditions, negated conditions, case equality, four-state producer values,
same-time NBA conditions, trailing delays, while-loop rechecks and named-event
waits. Representative sole rows include:

* `chapter-12/12.4--wait-statement.sv`
* `chapter-12/12.6.3--wait-level-sensitive-wakes-when-true.sv`
* `chapter-12/12.7.4--while-wait-rechecks-four-state-producer-condition.sv`
* `chapter-4/4.9.4--nba-zero-delay-schedules-current-time-v3.sv`
* `chapter-9/9.4.3--wait-conjunction-unblocks-after-last-operand.sv`
* `chapter-9/9.4.3--wait-with-trailing-delay-statement.sv`

Reproduce the table with:

```text
python3.9 extractors/sv/wait_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it classifies wait source shapes without
sampling a condition, registering a dependency, advancing time or choosing a
wake-up order.
