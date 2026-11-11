# E Step 11: plain `always @*`

The clean-room sources are in
[`Examples/system-verilog/sem2/always_star_step11/`](../Examples/system-verilog/sem2/always_star_step11/).
They retain the parser's `ImplicitEventControl` and process body, rather than
converting the process into `always_comb`. The E-core-0 source entry now keeps
that node as an implicit process: the first case fixture executes in E, and the
startup fixture checks its time-zero distinction. The function-sensitivity
fixture remains loud at the function-call boundary.

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

The source-shaped E entry represents an implicit event-controlled process with
its body and source-derived read sensitivity. Process startup first suspends at
this event control. A change in a watched read schedules the existing E body
engine in Active; after the body completes, the process re-arms its implicit
wait. An empty read set never wakes. Input-port propagation is an event if the
source connection semantics generates one; the wait rule itself does not
invent an initial activation.

The E active scheduler notifies this wait after relevant writes. The same
existing body meaning handles blocking assignments and case statements. Plain
`@*` uses the body's raw reads, unlike `always_comb`, whose sensitivity removes
its own writes. Function sensitivity must consult retained call nodes; inlining
a function would silently broaden `@*` sensitivity. The `always_comb` startup
and function-read rules remain its own cases. This E-core-0 entry is a flat,
single-slot fragment; unsupported functions, clocked processes, hierarchy and
other constructs remain loud.

The first fixture's E proof checks the loaded `Proc0.implicit` node's
sensitivity and executes all twelve source stimuli, including its initial
wait. Its kernel trace is:

```text
xxxx 0011 | 0011 0011 | 1010 1010 | 0101 0101
1111 1111 | 0101 0101 | 1111 1111 | 1111 1111
xz01 xz01 | zzzz zzzz | xx11 xx11 | xxxx xxxx
```

The startup fixture's E guard checks the initial row
`xxxx,0110,xxxx,0110`, separating the plain `@*` wait and the
`always_comb` time-zero activation. The function-sensitivity fixture retains
the parser's `FunctionCall` nodes and refuses in E; no inlined or fabricated
function result is used.

Retained extraction emits `AlwaysEvent` with
`event_kind: "ImplicitEventControl"`. `Ingest2` now retains that event as
`PProcess.alwaysImplicit`, carrying the existing parsed `PStmt` body rather
than replacing the entire process by `unsupported`. It rejects contradictory
explicit event, edge, guard, clock, reset and source-style fields. Other
event-control kinds keep their existing loud boundary. This is source
ingestion, not a new activation rule.

The ordinary frozen `Process2` bridge still has no implicit-event process and reports
`ProceduralBlockSymbol:Always: source-level event-controlled always is
retained; the frozen process AST has no event-list constructor`.
The E entry is separate: `PDesign.instantiateE2` retains the parser node and
`Elab.ofEDesign2` maps it to `Proc0.implicit` without lowering it to
`always_comb`. `agree.lean` checks the retained case body, function fixture and
startup control, malformed event metadata, the exact refusal in each frozen
view, and the generated-process refusal in the retiring memory adapter.
Function declarations/calls and initialization have their additional existing
boundaries. No parallel body AST or shared judgment was introduced.

The older timed loader's `AlwaysImplicit` path currently starts with a ready
body (`Load.lean`, `timedProcOfRaw`), like `always_comb`. That startup is not
the implicit-wait rule above. It is legacy execution debt, not E evidence;
the correction belongs to the single source-AST/E migration.
