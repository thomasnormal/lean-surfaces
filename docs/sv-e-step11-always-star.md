# E Step 11: plain `always @*`

The clean-room sources are in
[`Examples/system-verilog/sem2/always_star_step11/`](../Examples/system-verilog/sem2/always_star_step11/).
They retain the parser's `ImplicitEventControl` and process body, rather than
converting the process into `always_comb`. The ordinary fixtures have an
E-core-0 execution receipt; the continuous-driver startup case is kept as a
source-shaped receipt with an explicit simulator schedule split.

IEEE 1800-2023 §9.4.2.2 defines the implicit event control; §9.2.2.2.2
distinguishes `always_comb` from `always @*`. In particular, `always_comb`
runs once at startup and includes reads inside called functions in its
inferred sensitivity. Plain `@*` first waits for a relevant event and
includes the function's actual-argument reads, not its hidden global reads.
The single-writer restriction on `always_comb` is also distinct from the
general `always` procedure's rules (§9.2.2.1).

## Sources and measured rows

`always_star_step11.sv` pairs `@*` and `always_comb` case bodies over symbolic
width `W`. Its twelve rows cover a change to an input read by an unselected
branch, known and x/z case labels, default behavior, and x/z on both data
operands. `always_star_function_sensitivity_step11.sv` adds twelve rows for a
function whose result depends on an argument and a module variable. After a
known argument event, changing only the hidden variable updates the
`always_comb` output and leaves the `@*` output unchanged. Function calls
remain explicit `FunctionCall` envelope nodes; this fixture does not inline
the function or admit its execution to E.

The first probe exposed a startup difference, retained as evidence rather
than counted as agreement. Testbench variable initialization precedes process
startup (§6.8), but the connected input ports add a propagation boundary. On
these exact source/testbench pairs, the observed `@*` values are:

| source / observation | Icarus 13.0 | Xcelium 24.03-s004 |
| --- | --- | --- |
| case source, first row | `xxxx` | `0011` |
| function source, first row | `xxxx` | `0110` |
| function source, hidden-only change | `xxxx` | `0110` |

The following function row samples a known argument event; the remaining
rows then agree. The checker records the three startup-dependent observations
separately, bound to SHA256 of source bytes, a NUL, and testbench bytes. It
fails any unrecorded trace difference or source change. These observations are
not declared standards-equivalent outcomes or an allowed E outcome set.
The port startup ordering still needs the source event/connection model's
analysis; no convenient simulator order is selected for a proof.

`always_star_startup_step11.sv` isolates the startup rule with initialized
variables in the same module, avoiding the input-port question. It also has
a constant-only body, whose implicit sensitivity set is empty. Both
simulators agree on all five rows (columns `y_star`, `y_comb`,
`y_constant_star`, `y_constant_comb`):

| action | `y_star` | `y_comb` | `y_constant_star` | `y_constant_comb` |
| --- | --- | --- | --- | --- |
| first | `xxxx` | `0110` | `xxxx` | `0110` |
| change `a` to `1010` | `1111` | `1111` | `xxxx` | `0110` |
| change `b` to `1001` | `0011` | `0011` | `xxxx` | `0110` |
| change `a` to `xz01` | `xx00` | `xx00` | `xxxx` | `0110` |
| change `b` to `zzzz` | `xxxx` | `xxxx` | `xxxx` | `0110` |

Across the three sources, each simulator supplies 26 common rows and three
separately reported startup observations. Xcelium passes the readiness gate;
versions are printed. These are four-state simulator observations, not a
proof over every resolution or an E trace.

```sh
lake build 'Examples.«system-verilog».sem2.always_star_step11.agree'
python3 Examples/system-verilog/sem2/always_star_step11/check.py
```

## E rule and remaining boundary

The single source AST needs an implicit event-controlled process with its
own style, body and source-derived read sensitivity. The memory E profile now
implements the acyclic slice used by the runtime-memory receipt: process
startup waits, a change in a watched read schedules the retained body in the
active pass, and the body is blocking. A watched `mem[i]` contributes both
the selected cell and the index expression, so a write to another cell does
not wake it. Input changes are compared with the complete pre-slot state,
before edge commits and continuous assignments are considered. A body runs at
most once in one pass; if it changes one of its own watched reads, E refuses
the re-arm instead of silently dropping an event.

The admitted statement slice is blocking scalar or one-rank memory assignment
inside `if` and source blocks. Case statements, procedural loops, NBAs and
other statement nodes remain explicit boundaries. Function sensitivity must
consult retained call nodes; inlining a function would silently broaden `@*`
sensitivity. The `always_comb` startup and function-read rules remain their own
cases. Input-port propagation is an event if the source connection semantics
generates one; the wait rule itself does not invent an initial activation.

Retained extraction emits `AlwaysEvent` with
`event_kind: "ImplicitEventControl"`. `Ingest2` now retains that event as
`PProcess.alwaysImplicit`, carrying the existing parsed `PStmt` body rather
than replacing the entire process by `unsupported`. It rejects contradictory
explicit event, edge, guard, clock, reset and source-style fields. Other
event-control kinds keep their existing loud boundary. This is source
ingestion, not a new activation rule.

The frozen `Process2` bridge still has no implicit-event process and reports
`ProceduralBlockSymbol:Always: source-level event-controlled always is
retained; the frozen process AST has no event-list constructor`.
`agree.lean` checks the retained case body, function fixture and both startup
controls, malformed event metadata, and the exact refusal in each frozen
view. The source-shaped memory adapter now admits the narrow body slice and
rejects every other process or statement shape before execution, so an
unsupported process cannot be silently skipped. Function declarations/calls
and initialization have their additional existing boundaries. The loaded
source E trace and its simulator comparisons are covered by the memory-read
receipt below; the full event/frame proof remains required.

The older timed loader's `AlwaysImplicit` path currently starts with a ready
body (`Load.lean`, `timedProcOfRaw`), like `always_comb`. That startup is not
the implicit-wait rule above. It is legacy execution debt, not E evidence;
the correction belongs to the single source-AST/E migration.

## Continuous-driver time-zero boundary

[`always_star_timezero_e`](../Examples/system-verilog/sem2/always_star_timezero_e/)
is the minimal source shape that previously hit the R3 refusal: a plain
`always @*` reads `k` while a continuous assignment drives `k` at time zero.
The extractor now retains the parser's `AlwaysEvent` node and its body for E;
it does not lower the process to `always_comb`. E's `σ_src` receipt produces
`0011` for `y_star` on the first row and follows the changed input thereafter.

The differential checker records the same source under Icarus 13.0 and
Xcelium 24.03-s004. Icarus leaves `y_star=xxxx` on the first row, while
Xcelium produces `0011`; all later known/x/z rows agree. This is the
time-zero Active-region ordering freedom of §4.7. The receipt is therefore
not an exact-equivalence claim for that first observation, and neither tool's
startup order is selected as the language meaning.

## Runtime unpacked-memory read boundary

[`always_star_memory_read_e`](../Examples/system-verilog/sem2/always_star_memory_read_e/)
is the source-shaped E receipt: a plain `always @*` reads `mem[ridx]`
from a parameter-sized unpacked memory while an edge process writes
`mem[widx]`. The extractor now retains the parser's `ArraySel` with its
`unpacked` metadata and the implicit event node. It never expands the
parameterized array into cells or fabricates scalar sensitivity.

The E memory profile retains the parser's body and executes it after the
selected cell or index changes. Its nine-row receipt covers initial x state,
two writes and runtime reads, an untouched cell, and x/z indices. Icarus
Verilog 13.0 and readiness-gated Xcelium 24.03-s004 agree on all nine rows.
This is the admitted acyclic scheduler slice; self-retriggering, case/loop
bodies and other unsupported process shapes remain loud. The next PicoRV32
probe records the first such boundary rather than bypassing it.

## Case execution boundary

[`always_star_case_latch_e`](../Examples/system-verilog/sem2/always_star_case_latch_e/)
is the next source-shaped boundary: a plain `always @*` with a `case` that
has no `default`.  The extractor retains `AlwaysEvent` with
`event_kind: "ImplicitEventControl"`, preserves the `PStmt.caseStmt` and its
source-order arms, and carries the R5 missing-assignment reason.  It does not
add a default arm or lower the case into an `if` chain.  The retained case
node is the next E execution wall; it is not lowered into an `if` chain.

The E memory profile admits the implicit process but still rejects its case
body with `E implicit body case execution is outside the current memory
profile`, before execution.  The fixture's rows cover a matching arm,
unmatched selectors, an x/z selector, data changes while unmatched, and hold
after the last capture.  Icarus Verilog 13.0 leaves the first `q` sample
`xxxx`, while readiness-gated Xcelium 24.03-s004 reports `0011`; this is the
same §4.7 startup-order split.  The remaining seven rows match exactly in
both tools.
