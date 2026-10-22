# Continuous-assignment delays — repricing boundary

IEEE §§10.3, 10.3.3 and 4.9.1 allow a delay control on a continuous
assignment itself. The driver evaluates the RHS and schedules its output;
rise/fall and optional turn-off values select the publication delay for the
transition. The initial driven value is delayed as well. Inertial behavior
cancels or replaces a pending event when a later RHS value changes the
scheduled result, and strength syntax is ordered before the delay control.

## Why continuous-assignment delays remain a boundary

The public envelope has no delayed continuous-driver queue, pending-value
identity, inertial cancellation state, transition selector or strength-aware
publication record. Lowering `assign #d` to an immediate assignment exposes
short pulses and changes initial X settling and subsequent event order. The
tier therefore keeps `ContinuousAssignSymbol:delay` loud and introduces no
second scheduler.

## 2026-10-22 census and decision

The fresh 22,043-path census records `ContinuousAssignSymbol:delay` in **21**
files: **13** are continuous-assignment-delay-only and **8** co-occur with
another wall. Repricing the sole files finds **13** spans: all are delayed
assignments, **6** specify rise/fall values, **4** specify three delay values,
**4** target vectors, **4** exercise inertial cancellation or rescheduling,
**2** contain a four-state `z` transition, **3** cover initial-X settling,
**1** tests strength-before-delay ordering and **1** is a chapter-37 type form
(features overlap).

Reproduce the table with:

```text
python3.9 extractors/sv/continuous_assign_delay_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it reports delayed-assignment source shapes
without scheduling a driver output or selecting a transition delay.
