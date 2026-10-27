# Call statements — admitted boundary

This document fixes the public boundary for statement-position calls in the
SystemVerilog envelope. A statement call is an effectful operation: the
surface must describe its state, output, scheduling, and termination effects,
not merely parse its argument expressions. Expression-position queries such
as fixed `$bits` and runtime `$clog2` have separate contracts and are not part
of this wall.

## Admitted statements

Discarded `$sformatf` calls are inert when the existing expression converter
accepts one literal format and one pure integral operand. The `%b`, `%h`,
`%o`, and `%d` conversions (including uppercase aliases) are evaluated only
to establish that the call is pure, then erased because statement position
does not observe the packed result. Dynamic formats, extra arguments,
unsupported conversions, real or aggregate operands, and other string state
remain loud.

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

An invalid literal mode in a discarded `$fopen(path, mode)` call is also inert
after the existing file converter confirms the path and mode. IEEE
1800-2023 §21.3.1 specifies the zero return for a rejected mode before file
access; valid or dynamic modes and value-position calls remain loud at the
file-state boundary.

Discarded `num()` and `size()` queries on an untouched 2-state associative
array are inert after the existing empty-array converter proves their exact
zero result. Populated, aliased, initialized, dynamic, and value-position
queries remain loud because their count is runtime state.

Discarded `first(index)` and `last(index)` queries on an untouched 2-state
associative array follow the same empty-array rule. The direct named index
argument is still checked by the existing converter; populated arrays and
effectful or computed indices remain loud.

Discarded `size()` on an untouched queue or dynamic array, and `len()` on an
untouched empty string, are inert after the existing zero-size converter proves
their scalar zero. Any mutation, alias, or value-position observation remains
loud because the receiver's size is then runtime state.

Discarded `len`, `getc`, `atoi`, radix, `compare`, and `icompare` calls on
unchanged ASCII literal strings are also inert after their existing source
history converters validate the receiver and arguments. Non-ASCII, dynamic,
mutated, aliased, and unsupported string operations remain loud.

A discarded `atoreal()` conversion from a proven ASCII literal is likewise
inert because the tier has no represented real storage. Dynamic strings,
nonliteral writes, and value-position real conversions remain loud.

A discarded `event.triggered()` query on an untouched event is inert after the
existing converter proves its pre-trigger false result. Triggered events,
dynamic handles, and value-position queries remain loud at the event-state
boundary.

A discarded `enum.name()` query is inert after the existing enum method
converter validates its receiver and declaration-order cases. Numeric enum
methods, effectful receivers, malformed calls, and value-position queries
retain their existing boundaries.

Discarded numeric enum methods (`first`, `last`, `num`, `next`, and `prev`)
use the same pure converter and are erased after the receiver and step checks
pass. Dynamic or effectful receivers, malformed methods, and value-position
calls remain on their ordinary enum boundary.

Discarded `toupper()`, `tolower()`, and literal-bound `substr()` calls on a
proven ASCII string likewise erase their fresh string result after the existing
source-history check. Dynamic, aliased, mutated, non-ASCII, symbolic, and
value-position string transformations remain loud.

Discarded `min()`, `max()`, `unique()`, and `unique_index()` queries on a named
fixed-size integral array are also inert with no `with` clause or with a
source-pure integral `with` expression. The returned queue is unobserved;
dynamic, queue, associative, aggregate, effectful `with`, symbolic, and
value-position forms remain loud.

Discarded fixed-array reductions (`sum`, `product`, `and`, `or`, and `xor`)
reuse the balanced reduction lowering after its storage-shape, width, iterator,
and purity checks. The existing empty-dynamic-array identity also permits
discarded `sum` and `product`; other dynamic storage, effectful `with`
expressions, and value-position reductions remain loud.

Discarded `delete()` calls on an empty queue or an uninitialized dynamic array
are also inert. The receiver history is restricted to `delete()` and zero-size
queries (plus empty queue pops); initialized, populated, aliased, effectful,
and value-position aggregate operations remain loud.

An untouched 2-state associative array admits the same discarded `delete()`
no-op for the whole array or a source-pure integral/string key. Later `num()`
and `size()` queries remain exact; initialized, four-state, effectful-key,
aliased, and value-position forms remain loud.

Two source-pure `$q_initialize` calls for one queue ID are admitted when both
use the same literal FIFO/LIFO type and positive capacity, and the ID is a
single direct literal assignment when named. The first status is 0 and the
duplicate status is 6; no queue object is exposed. Other queue tasks,
invalid-first-creation duplicates, reassignment, computed IDs, and
value-position forms remain loud.

`$q_remove` status-only calls are admitted for an uninitialized literal queue
ID (status 2) or for a newly initialized, still-empty FIFO/LIFO queue (status
3). Job and inform outputs must remain unread, and the queue ID may be named
only after one direct literal assignment. Populated queues, payload reads,
additional queue operations, computed IDs, and value-position forms remain
loud.

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

## Named literal queue history for `$q_exam` — 2026-10-27

`$q_initialize`, `$q_add`, and `$q_exam` status writes may use a named queue,
job, or inform operand when source order proves exactly one prior direct
blocking literal assignment. The queue model still stores no payload: statistic
codes 1 and 3 derive current and maximum length from successful adds, then
write status 0. An unassigned, computed, timed, nonblocking, or reassigned
operand, a removal, another statistic code, or a value-position call remains
`Unsupported`. The `q_exam_stat_codes` fixture pins the two statistic codes and
the named-history transcript.

## Refusal boundary

All other statement-position calls remain `Unsupported` with their source
text. The boundary is intentional:

* `$strobe` and `$monitor` publish in Postponed and need the scheduler's
  read-only region and registration rules;
* `$fatal`, `$error`, `$warning`, and `$info` require a diagnostic channel,
  severity and termination/status semantics that `Out` does not represent;
* queue tasks, array methods, and PLA tasks mutate aggregate or modeled device
  state not present in the scalar/packed/fixed-cell store, except for the
  source-pure empty aggregate deletions admitted above;
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

## Duplicate queue-ID status — 2026-10-27

Two source-pure `$q_initialize` calls for one queue ID now lower to scalar
status writes: a valid first FIFO/LIFO creation returns 0 and the duplicate
returns 6. A named ID is accepted only after one direct literal assignment;
computed, reassigned, invalid-first-creation, and other queue operations remain
loud. The `q_initialize_duplicate_status` fixture supplies the differential
row and extractor/Lean receipts.

## Queue-add status — 2026-10-27

Source-pure `$q_add` calls after one literal FIFO/LIFO initialization now lower
to scalar status writes. Literal or prior-written named job and inform
arguments publish status 0 while the queue has capacity and status 1 for the
first add after it is full. Queue storage, unresolved or recomputed IDs, payload
expressions, additional queue operations, and value-position forms remain loud.
The `q_add_status_0` and
`q_add_status_1_when_full` fixtures supply the differential rows and
extractor/Lean receipts.

## Queue-full status — 2026-10-27

Literal `$q_full` queries after one literal queue initialization now lower to
scalar status 0 below capacity and 1 at capacity. Direct output statements and
value-position queries with an unread status output are admitted; symbolic IDs,
observed status writes, other queue operations, and payload expressions remain
loud. The `q_full_status_0` and `q_full_status_1_when_full` fixtures supply the
differential rows and extractor/Lean receipts.

## Queue-exam length statistics — 2026-10-27

Source-pure `$q_exam` calls with literal statistic code 1 or 3 now lower to a
two-write block: the current or maximum length derived from preceding literal
adds, followed by status 0. Queue IDs may be names with one prior direct
literal assignment. The count is clamped at the literal queue capacity.
Removal, timing, unresolved or recomputed IDs, other statistic codes, and
value-position forms remain loud. The five `q_exam_*` fixtures supply the
differential rows and Lean receipts.

## Queue-removal status — 2026-10-27

Undefined literal queue IDs now lower `$q_remove` to status 2. A valid literal
FIFO/LIFO initialization followed by one removal from the still-empty queue
lowers the initialization to status 0 and the removal to status 3. Job and
inform outputs must be unread; populated, payload-observing, computed, and
additional queue forms remain loud. The `q_remove_status_2` and
`q_remove_status_3` fixtures supply the differential rows and Lean receipts.

## Queue-removal payload — 2026-10-27

One source-ordered literal FIFO or LIFO queue may now add literal job/inform
pairs and remove a nonempty entry. The extractor snapshots the queue history
and lowers each removal to scalar writes for the returned job, inform, and
status, preserving FIFO/LIFO order and capacity. Dynamic IDs or payloads,
empty removals, branches, timing, other queue operations, and value-position
forms remain loud. The `q_remove_payload` fixture supplies the differential
row and Lean receipt.

## Discarded `$dumpportsflush()` — 2026-10-27

The no-argument `$dumpportsflush()` task is now erased as an inert VCD
operation in the self-check state. It only flushes an external port-waveform
buffer, which is outside the `PASS`/`FAIL` transcript; the argumented task and
all other port-dump operations remain loud until that external stream is
modeled. The `dumpportsflush_statement` fixture supplies the differential row
and Lean receipt.

## Literal queue initializer `.size()` — 2026-10-27

A 2-state queue initialized by a scalar-literal concatenation or assignment
pattern now answers `.size()` with the exact element count. The queue object
itself remains outside the flat self-check state, so pushes, pops, deletes,
aliases, content reads, dynamic initializers, and value-position aggregate
operations remain loud. The `queue_literal_size` fixture supplies the
differential row and Lean receipt.
