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

A discarded `$isunbounded` query is also inert for a literal or bounded
parameter operand. The existing expression rule proves the one-bit result is
zero, and statement position observes no value. Ordinary variables, unbounded
parameters, malformed calls, and value-position queries remain loud.

A discarded `$clog2` query is inert whenever the existing expression
converter accepts its operand. This preserves the converter's source-effect
checks while dropping an unobserved pure result; malformed or effectful forms
remain loud.

Valid discarded `$signed` and `$unsigned` calls are inert after the existing
signing converter accepts their integral operand. The statement boundary keeps
all operand and width checks, while malformed, aggregate, real, or effectful
forms remain loud.

Valid discarded `$timeunit` and `$timeprecision` calls are inert after the
existing metadata converter accepts a literal `` `timescale `` directive.
Missing directives, malformed metadata, and value-position forms remain loud.

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

A `$rtoi` statement with one finite real or short-real literal is also erased:
its signed 32-bit conversion result is discarded, so the pure operation has no
observable effect. Dynamic real reads, out-of-range literals, and other
argument shapes remain loud and use the expression-call boundary.

A discarded `$realtobits` call with one direct finite real literal is likewise
erased. The value-position form carries the exact IEEE-754 bit pattern; dynamic
storage and explicit conversion shells remain loud.

The same discarded-result rule applies to `$shortrealtobits` for a direct
literal passed through its implicit single-precision conversion shell. Explicit
casts, dynamic values, and overflow remain loud.

A discarded `$itor` call with one direct finite integral literal is also erased:
integer-to-real conversion is exact and its real result has no represented
storage. Named and computed operands remain loud.

A discarded `$bitstoreal` call with one known 64-bit integral literal is erased
for the same reason. Unknown and dynamic bit patterns remain loud.

The single-precision `$bitstoshortreal` call follows the same rule for one
known 32-bit integral literal; unknown and dynamic patterns remain loud.

Fixed-type `$size`, `$high`, `$left`, `$right`, `$low`, `$increment`,
`$dimensions`, and `$unpacked_dimensions` calls are also inert in statement
position when their metadata query is valid and the result is discarded. The
existing query converter proves fixed dimensions without evaluating the
operand; dynamic arrays, selectors, effectful operands, malformed calls, and
value uses remain on their ordinary boundaries.

Zero-argument `$time` and `$stime` calls are inert at the time-zero boundary
when their integer result is discarded. The exact zero-literal converter is
reused; argumented, delayed, and value-returning time queries remain loud.

The same discarded-result rule admits a zero-argument `$realtime` call at time
zero. Its real value is not represented; argumented, delayed, and value forms
remain loud at the real/time boundary.

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

## Discarded empty queue pops — 2026-10-25

The direct statement forms `void'(q.pop_front())` and
`void'(q.pop_back())` are admitted when source order proves that `q` is an
uninitialized or empty queue. IEEE 1800-2023 §§7.10.2.4–7.10.2.5 specify that
an empty pop has no effect on the queue, so erasing the discarded result is
exact in the flat self-check state. A queue with a push, alias, dynamic
receiver, or other operation remains a loud `ExpressionStatement:CallExpression`;
value-position pops continue to use their separate default-value lowering.
