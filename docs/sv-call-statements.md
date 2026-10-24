# Call statements — admitted boundary

This document fixes the public boundary for statement-position calls in the
SystemVerilog envelope. A statement call is an effectful operation: the
surface must describe its state, output, scheduling, and termination effects,
not merely parse its argument expressions. Expression-position queries such
as fixed `$bits` and runtime `$clog2` have separate contracts and are not part
of this wall.

## Admitted statements

The legacy/self-check and scheduler-facing paths share one `SysCall` shape for
the four calls whose effects are represented by the existing output and halt
state:

* `$display` evaluates its arguments and appends one rendered line;
* `$write` evaluates its arguments and appends without adding a newline; and
* `$finish` and `$stop` halt the current run while retaining prior state,
  queued nonblocking work, and collected output.

`$display` and `$write` require a literal format string when arguments are
present; the remaining arguments are pure admitted integral expressions with
parallel signedness metadata. A bare output call is an empty write or line.
The ordinary `$cast` statement has its own dynamic-cast lowering and therefore
does not rely on the generic call-statement admission.

A zero-argument user function whose complete body is one integral literal
`return` is also admitted in statement position by erasing the discarded
result. The literal-only body has no storage, timing, diagnostic, or argument
effects. User calls with arguments, reads, operators, nested calls, or any
other body remain loud until callable frames are represented.

Literal `$timeformat` calls with no `%t` consumer in the source are erased as
inert configuration. The self-check surface has no time-format renderer, so
the setting cannot affect an observable result in that restricted shape;
dynamic arguments and sources that use `%t` remain loud.

Literal `$assertcontrol` calls with one or more integral literal arguments are
likewise erased. They change only assertion reporting controls, and the
self-check state has no assertion control register. Dynamic or hierarchical
arguments remain loud.

The self-check executor runs these calls at time zero. The retained stepper
delegates the same `SysCall` leaves to that executor after a delay or event
wait, so no second call interpreter is introduced. The scheduler's existing
region rule determines when output becomes observable.

## Refusal boundary

All other statement-position calls remain `Unsupported` with their source
text. The boundary is intentional:

* `$strobe` and `$monitor` publish in Postponed and need the scheduler's
  read-only region and registration rules;
* `$fatal`, `$error`, `$warning`, and `$info` require a diagnostic channel,
  severity and termination/status semantics that `Out` does not represent;
* queue tasks, array methods, and PLA tasks mutate aggregate or modeled device
  state not present in the scalar/packed/fixed-cell store;
* dump, file, memory, string-format, SDF, and timescale tasks perform external
  I/O or simulator configuration;
* `std::randomize` is nondeterministic and needs an explicit random oracle;
  assertion controls and program `$exit` need assertion/program state; and
* user subroutine calls and other methods need callable frames, receiver
  state, or hierarchy that this statement surface does not provide.

Admitting one of these calls by treating it as `$display` or `$finish` would
silently change observable diagnostics, status, scheduling, or state. The
surface therefore remains loud until the required representation is supplied.

## 2026-10-21 census and decision

The fresh 22,043-path census records
`ExpressionStatement:CallExpression` in **3,791** files: **261** are
call-only refusals and **3,530** co-occur with another refusal. The most common
companions are `VariableSymbol:2state` (2,243 files),
`AssignmentExpression:target` (1,240), `CallExpression` (1,191),
`SubroutineSymbol:Subroutine` (803), `NamedValueExpression:2state` (587), and
`CovergroupType:CovergroupType` (531). Companion counts overlap.

The call-only repricer finds **498** unsupported statement-call instances in
those 261 files. The largest heads are:

| source head | instances | files |
|---|---:|---:|
| `$fatal` | 74 | 34 |
| `$q_add` | 46 | 25 |
| `$q_initialize` | 34 | 33 |
| `$dumpvars` | 30 | 29 |
| `$strobe` | 29 | 25 |
| `$dumpfile` | 27 | 27 |
| `$monitor` | 20 | 16 |
| `$info` | 19 | 18 |
| `$q_remove` | 19 | 17 |
| `$warning` | 17 | 16 |
| `$assertcontrol` | 14 | 6 |
| `$q_exam` | 12 | 10 |
| `$async$and$array` | 12 | 12 |
| `$error` | 10 | 10 |
| `$dumpflush` | 8 | 8 |

The remaining 136 instances are a long tail of other dump, monitor, queue,
PLA, file, memory, SDF, assertion, program, method, and randomization calls.
No call-only head has the complete effect representation needed for an
independent legacy admission in this item. Existing `$display`/`$write`/
`$finish` tests remain the acceptance evidence; every other statement call
stays loud.

Reproduce the call-only table with
`python3.9 extractors/sv/call_reprice.py --corpus <corpus>/tests`; the tool
reads sources in process and writes no envelopes beside the corpus.
