# Dynamic delay expressions — repricing boundary

IEEE §§9.4.1, 5.8, 3.14.2.3 and 22.4 allow a delay control to use a
parameter, signal or arithmetic expression. The expression is sampled when
the process encounters the control. Fixed-point and unit-suffixed time
literals are converted using the active timeunit/timeprecision precedence;
unknown or high-impedance delay values become zero. A delay before a blocking
assignment retains the assignment until the delay completes.

## Why delay expressions remain a boundary

The public timed envelope admits only a nonnegative integral literal below
`2^64`. It has no runtime expression evaluator for delays, timeunit and
timeprecision environment, fixed-point conversion, X/Z-to-zero rule or
source-positioned delayed assignment continuation. Replacing a dynamic delay
with a guessed constant changes both elapsed time and the value sampled after
the wait. The tier therefore keeps `TimedStatement:DelayControl:expression`
loud and introduces no second time wheel.

## 2026-10-22 census and decision

The fresh 22,043-path census records
`TimedStatement:DelayControl:expression` in **168** files: **20** are
delay-expression-only and **148** co-occur with another wall. Repricing the
sole files finds **24** spans: **10** dynamic parameter or signal references,
**10** fixed-point forms, **9** unit-suffixed time literals, **15**
timeunit/timeprecision or rounding contexts, **3** X/Z-to-zero cases, **4**
delayed-assignment forms, **3** arithmetic expressions and **4** time-query
contexts (features overlap).

Reproduce the table with:

```text
python3.9 extractors/sv/delay_expression_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it classifies delay source shapes without
evaluating an expression, choosing a time scale or scheduling a continuation.
