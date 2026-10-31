## Whole packed-aggregate copies — 2026-10-28

The legacy self-check tier now lowers direct blocking copies between untagged
packed structs and packed unions through their existing flat vector cells.
Tagged aggregates and effectful or unsupported sources remain loud; no aggregate
heap or scheduler rule is added. The `packed_aggregate_copy` fixture, extractor
regressions, generated envelope, Lean receipt, and differential row cover the
new target family.

Differential coverage grows **420/414/0/6 → 421/415/0/6**; the committed
external corpus snapshot is unchanged because the checkout is unavailable.

# The SystemVerilog tier: FOUNDING CHARTER

## Logical negation of vector `iff` guards — 2026-10-31

Logical negation of an admitted packed vector, such as `iff !en[1:0]`, now uses
the existing vector truthiness before the unary operation. The
`always_ff_event_iff_vector_not` witness covers nonzero and zero vectors.
Differential coverage grows **560/546/0/14 → 561/547/0/14**; grammar coverage
remains **240/212/28**.

## Constant replication `iff` guards — 2026-10-31

Constant replications of admitted guard parts, such as `iff {2{en}}`, now use
the existing `SExpr.concat` truthiness path. Calls and other aggregate
selectors remain loud. The `always_ff_event_iff_replication` witness covers
disabled and enabled edges. Differential coverage grows **559/545/0/14 →
560/546/0/14**; grammar coverage remains **240/212/28**.

## Packed concatenation `iff` guards — 2026-10-31

Concatenations of admitted scalar or packed-select parts, such as
`iff {en[1], en[0]}`, now use `SExpr.concat` and vector truthiness. Replications
and other aggregate selectors remain loud. The `always_ff_event_iff_concat`
witness covers disabled and enabled clock edges. Differential coverage grows
**558/544/0/14 → 559/545/0/14**; grammar coverage remains **240/212/28**.

## Descending dynamic packed-vector `iff` guards — 2026-10-31

Descending dynamic packed part-selects such as `iff en[idx -: 2]` now use the
existing `SelectRead` direction and vector truthiness. Aggregate selectors
remain loud. The `always_ff_event_iff_dynamic_neg` witness covers disabled and
enabled clock edges. Differential coverage grows **557/543/0/14 →
558/544/0/14**; grammar coverage remains **240/212/28**.

## Ascending dynamic packed-vector `iff` guards — 2026-10-31

The timed guard slice admits ascending dynamic packed part-selects such as
`iff en[idx +: 2]` through the existing `SelectRead` evaluator and vector
truthiness. Descending dynamic and aggregate selectors remain loud. The
`always_ff_event_iff_dynamic` witness covers disabled and enabled edges.
Differential coverage grows **556/542/0/14 → 557/543/0/14**; grammar coverage
remains **240/212/28**.

## Constant packed-vector `iff` guards — 2026-10-31

The timed guard slice admits constant-index packed-vector `SelectRead` guards,
such as `iff en[1:0]`, using the existing vector truthiness in
`eventGuardPass`. Dynamic indexed and aggregate selectors remain loud. The
`always_ff_event_iff_vector` witness covers the disabled and enabled edges.
Differential coverage grows **555/541/0/14 → 556/542/0/14**; grammar coverage
remains **240/212/28**.

## Scalar guards on asynchronous-reset edges — 2026-10-31

The timed `always_ff` envelope retains `reset_iff` for a scalar guard on the
asynchronous reset event, alongside the existing clock-event `iff`. The
existing `ProcState.resetGuard` and `wakeEdges` path sample the reset guard only
when its reset edge is published; unsupported guard expressions remain loud.
The `always_ff_async_reset_iff_reset` witness covers a disabled reset edge and
an enabled reset edge. Differential coverage grows **554/540/0/14 →
555/541/0/14**; grammar coverage remains **240/212/28**.

## Indexed scalar `iff` guards — 2026-10-31

The timed event guard slice admits a direct one-bit packed-vector select such
as `iff en[0]` on plain events, `always_ff` clocks, and the clock event of an
asynchronous-reset list. The existing `SelectRead` evaluator samples it at
publication; reset edges remain unconditional. Part-selects, dynamic or
aggregate selectors, and reset-side guards remain loud. The
`always_ff_async_reset_iff_bit` witness covers the disabled clock, reset, and
enabled clock sequence. Differential coverage grows **553/539/0/14 →
554/540/0/14**; grammar coverage remains **240/212/28**.

## Guarded asynchronous-reset lists — 2026-10-31

The timed loader retains a scalar `iff` guard on the clock event of
`always_ff @(posedge clk iff en or negedge rst_n)` and leaves the asynchronous
reset edge unconditional. Active-high reset lists use the same retained clock
guard with a positive reset edge. The existing scheduler is the sole authority
for both wake paths; a reset-side guard remains loud. The
`always_ff_async_reset_iff` witness checks a disabled clock edge, an unguarded
reset edge, and an enabled clock edge. Differential coverage grows
**552/538/0/14 → 553/539/0/14**; grammar coverage remains **240/212/28**.

## Scalar `iff` guards on negative-edge timed `always_ff` clocks — 2026-10-31

Timed `always_ff @(negedge clk iff en)` now retains both the negative-edge
clock and its scalar guard. The existing edge wake-up samples `en` at the
published falling edge before the body enters the ordinary Active/Inactive/NBA
path; a disabled falling edge leaves the process armed for the next one.
Compound guards and guarded clock-plus-reset lists remain loud.

The `always_ff_event_iff_neg` witness checks a disabled falling edge followed by
an enabled capture and MATCHes its pinned transcript. Differential coverage
grows **549/535/0/14 → 550/536/0/14**; grammar coverage remains **240/212/28**.

## Scalar comparison `iff` guards — 2026-10-31

Scalar equality and inequality expressions such as `iff en == 1'b1` are now
retained on plain timed events and `always_ff` clocks. The existing scheduler
evaluates the guard with four-state semantics at publication, so `x` and `z`
results leave the process suspended; calls, selects, and other unsupported
expressions remain loud.

The `always_ff_event_iff_cmp` witness checks a disabled edge followed by an
enabled comparison and MATCHes. Differential coverage grows **550/536/0/14 →
551/537/0/14**; grammar coverage remains **240/212/28**.

## Scalar logical `iff` guards — 2026-10-31

Logical guards such as `iff en && mode` and `iff en || mode` are now retained
on plain timed events and `always_ff` clocks. Publication evaluates their
four-state truth value through the same expression evaluator; unknown results
leave the registration armed. Calls, selects, and other unsupported guards
remain loud.

The `always_ff_event_iff_logic` witness checks a disabled logical guard followed
by an enabled edge and MATCHes. Differential coverage grows **551/537/0/14 →
552/538/0/14**; grammar coverage remains **240/212/28**.

## Scalar `iff` guards on timed `always_ff` clocks — 2026-10-31

Timed `always_ff @(posedge clk iff en)` retains the scalar guard on its
positive-edge clock registration. The existing edge wake-up samples `en` in the published
state before the body enters the ordinary Active/Inactive/NBA path, so a
disabled edge does not enqueue an NBA update. Compound guards, guarded
negative-edge clocks, and guarded clock-plus-reset lists remain loud, and the `always_ff` process kind stays
distinct from plain `always` event lists.

The `always_ff_event_iff` witness raises `clk` once with `en = 0`, enables the
guard, then raises it again and checks the NBA capture. Its transcript MATCHes;
differential coverage grows **548/534/0/14 → 549/535/0/14**, while grammar
coverage remains **240/212/28**.

## Scalar `iff` guards for timed `always` events — 2026-10-31

Plain timed `always` event entries may carry a scalar identifier `iff` guard.
The guard is retained beside its event and sampled against the published state
when the edge occurs; a false or unknown guard leaves the process registered
for the next event. The existing Active/Inactive/NBA slot loop remains the
only scheduler, and compound guards remain loud until their general
expression evaluator is modelled.

The `always_event_iff` witness first raises `clk` with `en = 0`, then enables
the guard and raises it again; only the second edge updates `q` and the pinned
transcript MATCHes. Differential coverage grows **547/533/0/14 → 548/534/0/14**;
grammar coverage grows **239/211/28 → 240/212/28** with the new
`IffEventClause` witness.

## Bare-signal event controls for timed `always` — 2026-10-31

Plain `always @(trigger)` now uses the same retained event registration as a
multi-signal list, with one `any`-edge entry. The process sleeps until the
signal changes, runs its body, and re-arms through the existing
Active/Inactive/NBA slot loop. `always_ff @(trigger)` and conditional `iff`
controls remain loud because their clocked or guarded contracts are separate.

The `always_event_bare` witness changes `trigger` after a delay and MATCHes its
pinned transcript. Differential coverage grows **546/532/0/14 → 547/533/0/14**;
grammar coverage remains **239/211/28**.

## Generic multi-signal event lists for timed `always` — 2026-10-31

Plain `always @(a or b)` event lists now retain every listed scalar signal and
its `any`, `posedge`, or `negedge` polarity. The process sleeps in one
multi-event registration, wakes when any listed edge is published, and
re-arms through the existing Active/Inactive/NBA slot loop. The scheduler's
single loop remains the authority; no polling or event-list-specific loop was
introduced.

`always_ff` keeps the narrower clock-plus-reset forms. Empty lists, compound
conditional events, non-scalar expressions, and unsupported three-event
clock/reset shapes remain loud; scalar identifier `iff` filters are retained
by the guarded-event rung above. The `always_event_list` witness checks a change on one of two
signals and MATCHes its pinned transcript. Differential coverage grows
**545/531/0/14 → 546/532/0/14**; grammar coverage grows
**239/210/29 → 239/211/28**.

## Active-high asynchronous reset for timed `always_ff` — 2026-10-31

Timed `always_ff @(posedge clk or posedge rst)` now retains a positive-edge
asynchronous reset alongside the clock. A reset edge wakes the same retained
body and uses the ordinary Active/Inactive/NBA publication path; the reset
polarity is stored with the process so an active-low reset remains distinct.
The legacy initial-only runner continues to refuse both reset forms, and no
second event loop is introduced.

The `always_ff_async_reset_high` witness asserts reset between clock captures,
checks the reset value, then verifies capture after release. Differential
coverage grows **544/530/0/14 → 545/531/0/14**; grammar coverage remains
**239/210/29**.

## Negative-edge timed `always_ff` — 2026-10-31

Timed `always_ff @(negedge clk)` now retains a negative-edge clock
registration and re-arms the same process after each body. The edge marker is
carried in the existing `AlwaysPosedge` envelope vocabulary for compatibility;
omitting it remains the positive-edge form. Both edges use the same
Active/Inactive/NBA scheduler and nonblocking publication path, with no
clock-specific shortcut. The legacy self-check runner continues to refuse
non-initial processes.

The `always_ff_negedge` witness changes data between two falling edges and
checks both captures. Differential coverage grows **543/529/0/14 →
544/530/0/14**; grammar coverage remains **239/210/29**.

## Asynchronous active-low reset for timed `always_ff` — 2026-10-31

Timed `always_ff @(posedge clk or negedge rst_n)` now retains both event
registrations in the existing scheduler. A negedge of the active-low reset
wakes the same process continuation, so its nonblocking reset assignment is
committed through the ordinary NBA path; a later positive clock edge captures
the released value. The event-list conversion is enabled for ordinary and
symbolic extraction, while the legacy initial-only self-check runner keeps the
construct loud with its explicit reset edge in the refusal.

The `always_ff_async_reset` witness checks reset between clock captures and
then verifies capture after release. It adds no reset-specific event loop or
shortcut. Differential coverage grows **542/528/0/14 → 543/529/0/14**;
grammar coverage remains **239/210/29**.

## Scheduler core rung — 2026-10-30 (publication closure)

Before adding another concurrent process family, the scheduler's ordering
surface is pinned against the declared self-check oracle. The existing loop is
the one authority: it drains Active, then Inactive, commits NBA, and iterates
until the slot closes; process order inside a region remains the explicit
`RegionOracle` choice. Two witnesses match that loop: blocking assignment is
visible in Active before a same-slot nonblocking assignment commits in NBA, and
an `initial` process observes two delayed iterations of a plain `always`.

The scheduler now retains one active `$monitor` registration and samples it in
Postponed, emitting on the first sample and on value changes before `$strobe`.
The deterministic zero-delay feedback
witness now publishes guarded NBA writes back into Active until `N=3`; the
unbounded toggle remains a fuel-bounded refusal. The `#0` inactive-region
witness now resumes in Inactive (`9.4.1`), while the `@*`/`@(posedge)`
double-change witness exercises publication after each blocking statement and
the NBA witness exercises publication after NBA commit; all three are
differential matches against their pinned reference transcripts. Timed
`$strobe` now queues and flushes in Postponed (`21.2`), so it observes the
final Active/NBA value; the `scheduler_region_outputs` row checks the
monitor-before-strobe ordering against its pinned transcript.

The scheduler-core rows move differential coverage **537/522/0/15 →
537/523/0/14** (rows/agree/disagree/recorded refusals) with this monitor
witness. The current grammar
census is **237/190/47** (witnesses/MATCH/REFUSE); the
`ImplicitEventControl` witness now matches after the timed implicit-sensitivity
route is admitted. The timed `always_comb`, continuous-assignment,
`always_latch`, and `always_ff` rungs are now landed; multiple-driver net
resolution remains a separate boundary.

## Level-sensitive `wait` — 2026-10-31

The retained scheduler now admits a literal `wait (condition)` in timed
processes. The condition is sampled at the wait site; a false or unknown
condition suspends the process, and publication of a signal in its static
read set requeues the retained continuation in Active for a fresh sample.
When the condition is already true, the process continues in the same Active
pass. The M0 self-check path and event-triggered waits remain loud, and no
second event loop or synthetic polling process was added.

The `wait_accept` witness covers a blocked initial process, a delayed signal
publication, and the resumed body. The time-zero self-check path can evaluate
an already-true condition, but still refuses a wait that would suspend; event
triggers remain loud. The measured differential and grammar coverage deltas
are recorded in the lane journal for this item.

## `always_comb` same-slot publication — 2026-10-31

The inferred-sensitivity process is now exercised after two blocking writes to
its source in one Active process. Both publications use the existing wake queue;
the final value is observed after the slot settles, with no polling or second
scheduler. `always_comb_double_write_timed` pins the transcript and keeps the
single scheduler authoritative for same-time propagation.

## Plain `always` timed conformance — 2026-10-30

The scheduler-facing conformance harness now drives retained plain `always`
processes through `elabTimedDesign` and the existing Active/Inactive/NBA slot
loop. A time-zero slot is followed by unit advances until `$finish` or the
bounded observation budget; the process body and its delayed tail are retained
between slots. The legacy self-check runner remains initial-only, while
`always_ff` witnesses stay on their separate boundary.

The `always_accept` fixture and timed differential row verify two repetitions
and the `ALWAYS PASS` transcript. The grammar census sends plain `Always` and
non-`always_ff` `AlwaysPosedge` witnesses through the timed runner, lifting
grammar coverage **235/122/113 → 235/159/76** and differential coverage
**518/506/0/12 → 519/507/0/12**. No continuous assignment, `always_comb`,
`always_latch`, or `always_ff` support is claimed by this item.

## `always_comb` timed conformance — 2026-10-30

`always_comb` now uses the scheduler's retained process table with inferred
implicit sensitivity. Each process runs once in Active at time zero, becomes
dormant, and wakes in Active when a signal read by its body changes. Written
signals are removed from that sensitivity set, dependent comb processes are
queued by the same wake path, and NBA commits use the same wake rule. Timing
controls inside an `always_comb` body remain loud because the construct's
execution cannot suspend on the ordinary edge/timer continuation.

The four timed witnesses cover initial execution plus blocking wake, NBA wake,
dependent comb propagation, and written-signal sensitivity exclusion. The
legacy self-check path still refuses `AlwaysComb`; the timed path is the only
admitted surface. Continuous assignment, `always_ff`, and `always_latch` remain
subsequent rungs. Differential coverage grows **526/509/0/17 →
530/513/0/17**; grammar coverage grows **236/159/77 → 236/160/76** as the
`AlwaysCombBlock` witness moves from REFUSE to MATCH.

## Continuous assignment timed conformance — 2026-10-30

The timed path now admits a single-driver continuous `assign` as a dormant
combinational process. Its RHS is evaluated in Active at time zero and again
when an inferred read signal changes, and dependent assignments propagate
through the same scheduler queue. Multiple drivers remain loud: the scheduler
does not yet retain per-driver values or apply IEEE four-state net resolution,
so a last-writer result would be unsound. Delays and selected or concatenated
continuous targets remain outside this rung.

The `assign_accept` and `assign_chain` witnesses cover time-zero evaluation and
dependent propagation; `assign_multiple_drivers` records the loud boundary.
Continuous assignment is the only new timed process family in this item. The
differential table grows **530/513/0/17 → 533/515/0/18** and the grammar
census grows **236/160/76 → 236/186/50** as continuous-assignment witnesses
move through the timed runner.

## `always_ff` and `always_latch` timed conformance — 2026-10-30

The timed loader now preserves `always_ff` as a distinct process kind while
using the existing retained `@(posedge clk)` continuation, and admits
`always_latch` as a level-sensitive dormant process. A latch body runs once at
time zero and wakes when an inferred read signal changes; a disabled latch
retains its previous value. The legacy self-check path continues to refuse
both process kinds. Procedural edge publication and asynchronous reset event
lists remain explicit scheduler boundaries.

The `always_ff_accept` and `always_latch_accept` witnesses cover process
admission and latch capture through the timed runner. This item adds no second
event loop or special scheduling path. Differential coverage grows
**533/515/0/18 → 535/517/0/18**; grammar coverage grows
**236/186/50 → 237/188/49**.

## Packed concatenation and replication witness — 2026-10-30

The legacy differential corpus now carries a compact admitted initial-process
witness for packed concatenation and integral replication, with four-state
values checked through the existing self-check interpreter.

Differential coverage grows **517/505/0/12 → 518/506/0/12**; grammar coverage
grows **235/120/115 → 235/122/113**, moving both concatenation productions
from continuous-assignment refusals to matched initial-process witnesses.

## Power-operator witness — 2026-10-30

The legacy differential corpus now carries a compact admitted initial-process
witness for four-state integral power, checking positive and zero exponents as
well as unknown base and exponent propagation. The existing signed, unsigned,
and zero-negative power fixtures remain in the corpus; the symbolic
continuous-assignment witness stays a recorded grammar refusal.

Differential coverage grows **516/504/0/12 → 517/505/0/12**; grammar coverage
remains **235/120/115**.

## Integral arithmetic witness — 2026-10-30

The legacy differential corpus now carries a compact initial-process witness
for `+`, `-`, `*`, `/`, and `%`, including an unknown add result, with a literal
`PASS` transcript.

Differential coverage grows **515/503/0/12 → 516/504/0/12**; grammar coverage
grows **235/118/117 → 235/120/115** in the regenerated census.

## Equality and relational comparison witness — 2026-10-30

The legacy differential corpus now carries a compact initial-process witness
for `==`, `!=`, `<`, `<=`, `>`, and `>=`, including unknown comparison
results, with a literal `PASS` transcript.

Differential coverage grows **514/502/0/12 → 515/503/0/12**; grammar coverage
remains **235/118/117** after regeneration.

## Binary bitwise witness — 2026-10-30

The legacy differential corpus now carries a compact initial-process witness
for binary `&`, `|`, and `^`, including X-propagating operands, with a literal
`PASS` transcript.

Differential coverage grows **513/501/0/12 → 514/502/0/12**; grammar coverage
grows **235/116/119 → 235/118/117** as the census gains an initial-process
witness for binary bitwise forms previously represented only by
continuous-assignment refusals.

## Integral-shift witness — 2026-10-30

The legacy differential corpus now carries a compact initial-process witness
for logical and arithmetic left/right shifts, including signed arithmetic
right-shift fill, with a literal `PASS` transcript.

Differential coverage grows **512/500/0/12 → 513/501/0/12**; grammar coverage
grows **235/115/120 → 235/116/119**.

## Unary logical-not witness — 2026-10-30

The legacy differential corpus now carries a compact initial-process witness
for logical-not over zero, one, and unknown four-state operands, with a literal
`PASS` transcript.

Differential coverage grows **511/499/0/12 → 512/500/0/12**; grammar coverage
remains **235/113/122**.

## Unary bitwise-not witness — 2026-10-30

The legacy differential corpus now carries a compact initial-process witness
for unary bitwise-not over known and X/Z-propagating four-state operands, with a
literal `PASS` transcript.

Differential coverage grows **510/498/0/12 → 511/499/0/12**; grammar coverage
remains **235/113/122**.

## Unary reduction witness — 2026-10-30

The legacy differential corpus now carries a compact initial-process witness
for `|`, `&`, and `^`, including known results and an X-propagating reduction,
with a literal `PASS` transcript.

Differential coverage grows **509/497/0/12 → 510/498/0/12**; grammar coverage
remains **235/113/122**.

## Unary-minus arithmetic witness — 2026-10-30

The legacy differential corpus now carries a compact initial-process witness
for unary minus over known and unknown four-state operands, with a literal
`PASS` transcript.

Differential coverage grows **508/496/0/12 → 509/497/0/12**; grammar coverage
remains **235/113/122**.

## Unary-plus arithmetic witness — 2026-10-30

The legacy differential corpus now carries the existing four-state unary-plus
arithmetic fixture, covering known, unknown, signed, wide, nested, and
concatenated operands with a literal `PASS` transcript.

Differential coverage grows **507/495/0/12 → 508/496/0/12**; grammar coverage
remains **235/113/122**.

## Logical conjunction and disjunction witness — 2026-10-30

The legacy differential corpus now carries a compact initial-process witness
for `&&` and `||`, checking true and false scalar outcomes with a literal
`PASS` transcript.

Differential coverage grows **506/494/0/12 → 507/495/0/12**; grammar coverage
remains **235/113/122**.

## Scalar conditional-expression witness — 2026-10-30

The legacy differential corpus now carries a compact initial-process witness
for scalar `?:` selection, checking both true and false branches with a
literal `PASS` transcript.

Differential coverage grows **505/493/0/12 → 506/494/0/12**; grammar coverage
remains **235/113/122**.

## Four-state case equality witness — 2026-10-30

The legacy differential corpus now carries a compact initial-process witness
for exact `===` and `!==` comparisons, including a matching X bit and a
nonmatching value, with a literal `PASS` transcript.

Differential coverage grows **504/492/0/12 → 505/493/0/12**; grammar coverage
remains **235/113/122**.

## Dynamic `inside` expression range witness — 2026-10-30

The legacy differential corpus now carries a compact dynamic `inside`
expression fixture with variable range endpoints, checking both a hit and a
miss before a literal `PASS` transcript. Runtime bounds use the existing
integral membership path without adding scheduler or aggregate state.

Differential coverage grows **503/491/0/12 → 504/492/0/12**; grammar coverage
remains **235/113/122**.

## Ordinary `inside` expression witness — 2026-10-30

The legacy differential corpus now carries a compact ordinary `inside`
expression fixture with scalar membership, range hit and miss checks, and a
literal `PASS` transcript. The existing integral membership predicates are
exercised directly outside a case chain.

Differential coverage grows **502/490/0/12 → 503/491/0/12**; grammar coverage
remains **235/113/122**.

## Typed local `let` formals — 2026-10-30

The legacy differential corpus now carries a compact typed local `let` witness
with repeated calls and literal `PASS` checks. Typed value-only formals reuse
the admitted let expansion path; effectful and unsupported forms retain their
existing loud boundaries.

Differential coverage grows **501/489/0/12 → 502/490/0/12**; grammar coverage
remains **235/113/122**.

## `let` defaults and named actuals — 2026-10-30

The legacy differential corpus now carries a compact pure local `let` witness
for default formal binding and reordered named actuals, with literal `PASS`
checks. The value-only let path stays admitted while effectful expansions and
subroutine calls retain their existing loud boundaries.

Differential coverage grows **500/488/0/12 → 501/489/0/12**; grammar coverage
remains **235/113/122**.

## Pure local `let` differential witness — 2026-10-30

The legacy differential corpus now carries a compact pure local `let` fixture
with repeated calls and literal `PASS` checks. Source-declared let expressions
remain value-only here; subroutine calls, side effects, and timed let bodies
stay at their existing loud boundaries.

Differential coverage grows **499/487/0/12 → 500/488/0/12**; grammar coverage
remains **235/113/122**.

## Dynamic `case (…) inside` range witness — 2026-10-30

The legacy differential corpus now carries a compact dynamic `case (…) inside`
fixture with variable range endpoints, matching and nonmatching paths, and a
literal `PASS` transcript. The existing membership lowering is exercised with
runtime bounds while source-order selection and the explicit default remain
unchanged.

Differential coverage grows **498/486/0/12 → 499/487/0/12**; grammar coverage
remains **235/113/122**.

## Ordinary `case (…) inside` differential witness — 2026-10-30

The legacy differential corpus now carries a compact ordinary `case (…) inside`
fixture with range membership and a literal `PASS` transcript. The existing
case-inside lowering is exercised through first-match range selection while
the default arm remains explicit.

Differential coverage grows **497/485/0/12 → 498/486/0/12**; grammar coverage
remains **235/113/122**.

## Wildcard `casez`/`casex` differential witness — 2026-10-30

The legacy self-check corpus now exercises the admitted wildcard case control
chain with a compact `PASS` fixture. `casez` ignores Z in either operand and
`casex` ignores X and Z, while source-order first-match selection is preserved.
The `wildcard_case_accept` fixture, generated envelope, and differential row
cover both predicates.

Differential coverage grows **496/484/0/12 → 497/485/0/12**; grammar coverage
remains **235/113/122**.


## Dynamic `priority if` no-fallback refusal witness — 2026-10-30

The legacy self-check tier now pins a dynamic `priority if` chain without a
final `else` as `ConditionalStatement:Priority`. A fallback makes the
no-match path unobservable and remains admitted; without it, the qualifier stays
loud. The `priority_if_dynamic_refuse` fixture, generated envelope, and
differential row record the refusal.

Differential coverage grows **495/484/0/11 → 496/484/0/12**; grammar coverage
remains **235/113/122**.


## Dynamic `unique if` refusal witness — 2026-10-30

The legacy self-check tier now pins a dynamic `unique if` chain as
`ConditionalStatement:Unique`. Distinct literal equalities with an explicit
`else` remain admitted; a dynamic condition leaves the multiple-match diagnostic
unresolved, so the qualifier stays loud. The `unique_if_dynamic_refuse` fixture,
generated envelope, and differential row record the refusal.

Differential coverage grows **494/484/0/10 → 495/484/0/11**; grammar coverage
remains **235/113/122**.


## Dynamic `unique0 case` refusal witness — 2026-10-30

The legacy self-check tier now pins a dynamic `unique0 case` label as
`CaseStatement:Unique0`. Literal, duplicate-free labels remain admitted because
`unique0` permits no match; a dynamic label leaves overlap behavior unresolved,
so the qualifier stays loud. The `unique0_case_dynamic_refuse` fixture,
generated envelope, and differential row record the refusal.

Differential coverage grows **493/484/0/9 → 494/484/0/10**; grammar coverage
remains **235/113/122**.


## `priority case` no-default refusal witness — 2026-10-30

The legacy self-check tier now pins the existing loud boundary for a dynamic
`priority case` without a `default`. The missing fallback leaves an observable
no-match diagnostic, so `CaseStatement:Priority` remains unsupported rather than
being erased into an ordinary first-match chain. The
`priority_case_dynamic_refuse` fixture, generated envelope, and differential row
record the refusal.

Differential coverage grows **492/484/0/8 → 493/484/0/9**; grammar coverage
remains **235/113/122**.


## Dynamic `unique case … inside` refusal witness — 2026-10-30

The legacy self-check tier now pins the existing loud boundary for a dynamic
`unique case … inside` with wildcard patterns. The extractor retains
`CaseStatement:Unique`; no qualifier diagnostic is fabricated and no first-match
lowering is claimed for this form. The `unique_case_dynamic_refuse` fixture,
generated envelope, and differential row record the refusal.

Differential coverage grows **491/484/0/7 → 492/484/0/8**; grammar coverage
remains **235/113/122**.


## Side-effecting `let` expansion refusal fixture — 2026-10-29

The differential corpus now pins the existing loud boundary for a `let`
template whose actual expands to side-effecting postfix increments. The
extractor retains `UnaryExpression:Postincrement` rather than inventing an
expression-order lowering; the row is a recorded refusal and protects that
decision. Differential coverage grows **490/484/0/6 → 491/484/0/7**; grammar
coverage remains **235/113/122**.

## Plain task-selected radix writes in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's marked flat-write
lowering for direct integral `$swriteb`, `$swriteo`, and `$swriteh` calls.
The converter has already checked the source history, radix spelling, and
destination width; selected or aggregate destinations remain loud. Across all
checked-in example sources, the adapter-only residuals
`Call:$swriteb`, `Call:$swriteo`, and `Call:$swriteh` fall **1 → 0** each.
Differential coverage remains **490/484/0/6** and grammar coverage remains
**235/113/122**.

## Plain literal `$sformat` assignments in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's marked flat-write
lowering for plain literal `$sformat` assignments to direct integral targets.
The converter checks the literal format and destination width before emitting
the represented write; selected/aggregate targets and `$swrite` remain loud.
The existing `sformat_literal_integral` fixture covers the admitted form.

Differential coverage remains **490/484/0/6** and grammar coverage remains
**235/113/122**. On the checked-in **1002-file** example sweep, the adapter
census moves **801 clean / 201 partial → 802 clean / 200 partial**; the sole
plain `$sformat` residual falls to zero.

## Predefined-stdout file output in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's existing lowering for
`$fdisplay` and `$fwrite` on the predefined stdout descriptors (`1` and
`32'h8000_0001`). The converter checks the descriptor, literal format, and
argument purity before mapping to the represented `$display`/`$write` state;
other descriptors and unsupported forms remain loud. The existing
`fdisplay_stdout`, `fdisplay_mcd_variable`, and `fwrite_stdout` fixtures cover
the admitted forms.

Differential coverage remains **490/484/0/6** and grammar coverage remains
**235/113/122**. On the checked-in **1002-file** example sweep, the adapter
census moves **798 clean / 204 partial → 801 clean / 201 partial**; the
`Call:$fdisplay` and `Call:$fwrite` residuals fall to zero. The two
`Call:$strobe` residuals remain scheduler-owned postponed-output cases.

## Repeated fixed-struct-array ordering keys — 2026-10-29

The legacy fixed-struct-array ordering lowering now accepts a repeated
`rsort with (...)` (or `sort with (...)`) call when its key matches the
preceding ordering call. The compatibility check compares the complete
argument-list payload at the correct syntax level; incompatible keys remain
loud. The existing `struct_array_ordering_with_field` envelope and receipt
cover ascending then descending ordering.

On the checked-in **1002-file** SystemVerilog example sweep, the adapter census
moves **797 clean / 205 partial → 798 clean / 204 partial** and `Call:rsort`
falls to zero. Differential coverage remains **490/484/0/6** and grammar
coverage remains **235/113/122**.

## Qualified `if` fallbacks in the adapter — 2026-10-29

The legacy adapter census now recognizes the extractor's
`qualified_fallback_lowered` lowering for `unique if` and `priority if` chains
with explicit fallbacks. Complete chains have no qualifier diagnostic and run
as ordinary adapter control; incomplete or overlapping forms remain loud. The
`pure_qualified_if_fallback_adapter` fixture, adapter regression, generated
envelope, Lean receipt, and differential row cover the admitted form.

Differential coverage grows **489/483/0/6 → 490/484/0/6**; grammar coverage
remains **235/113/122**. On the checked-in **1002-file** SystemVerilog example
sweep (**1001 files before this witness**), the adapter census moves **795 clean
/ 206 partial → 797 clean / 205 partial**; the existing qualified-if fallback
residuals are cleared.

## Discarded literal coverage queries in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's
`coverage_nocov_statement` marker for discarded literal coverage queries. With
no represented coverage database, these calls return the fixed empty-coverage
result and carry no adapter state; dynamic arguments and covergroup-backed
designs remain loud. The `pure_coverage_nocov_statements_adapter` fixture,
adapter regression, generated envelope, Lean receipt, and differential row
cover the admitted forms.

Differential coverage grows **488/482/0/6 → 489/483/0/6**; grammar coverage
remains **235/113/122**. On the checked-in **1001-file** SystemVerilog example
sweep (**1000 files before this witness**), the adapter census moves **794 clean
/ 206 partial → 795 clean / 206 partial**.

## Discarded stdout file-position errors in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's
`fseek_stdout_error_statement` and `ftell_stdout_error_statement` markers for
discarded file-position calls on the predefined stdout descriptor. The fixed
error results carry no represented adapter state; dynamic descriptors and
other arguments remain loud. The
`pure_stdout_position_error_statements_adapter` fixture, adapter regression,
generated envelope, Lean receipt, and differential row cover the admitted
forms.

Differential coverage grows **487/481/0/6 → 488/482/0/6**; grammar coverage
remains **235/113/122**. On the checked-in **1000-file** SystemVerilog example
sweep (**999 files before this witness**), the adapter census moves **793 clean
/ 206 partial → 794 clean / 206 partial**.

## Discarded invalid-literal `$fopen` calls in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's
`fopen_invalid_mode_statement` marker for discarded `$fopen` calls with an
invalid literal mode. The rejected call performs no represented filesystem
operation; dynamic modes and valid opens remain loud. The
`pure_fopen_invalid_mode_statements_adapter` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the admitted form.

Differential coverage grows **486/480/0/6 → 487/481/0/6**; grammar coverage
remains **235/113/122**. On the checked-in **999-file** SystemVerilog example
sweep (**998 files before this witness**), the adapter census moves **791 clean
/ 207 partial → 793 clean / 206 partial**; the existing `Call:$fopen`
residual is cleared.

## Discarded pure `string.atoreal()` calls in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's
`floating_string_atoreal_statement` marker for discarded `string.atoreal()`
conversions of source-pure ASCII strings. Dynamic, non-ASCII, and effectful
string histories remain loud. The `pure_string_atoreal_statements_adapter`
fixture, adapter regressions, generated envelope, Lean receipt, and
differential row cover the admitted form.

Differential coverage grows **485/479/0/6 → 486/480/0/6**; grammar coverage
remains **235/113/122**. On the checked-in **998-file** SystemVerilog example
sweep (**997 files before this witness**), the adapter census moves **789 clean
/ 208 partial → 791 clean / 207 partial**.

## Finite associative count, exists, and empty-delete statements in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's
`associative_count_statement`, `associative_exists_statement`, and
`associative_empty_delete_statement` markers for discarded finite associative
`num`/`size` and literal `exists` observations, plus deletes on untouched
associative arrays. Dynamic keys and effectful histories remain loud. The
`pure_associative_count_exists_delete_statements_adapter` fixture, adapter
regressions, generated envelope, Lean receipt, and differential row cover the
admitted forms.

Differential coverage grows **484/478/0/6 → 485/479/0/6**; grammar coverage
remains **235/113/122**. On the checked-in **997-file** SystemVerilog example
sweep (**996 files before this witness**), the adapter census moves **786 clean
/ 210 partial → 789 clean / 208 partial**.

## Finite associative endpoint and delete statements in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's
`associative_endpoint_statement` and `associative_delete_lowered` markers for
finite integral associative-array `first`/`last` statements and literal-key or
whole-array `delete` operations. Dynamic keys and effectful histories remain
loud. The `pure_associative_endpoint_delete_statements_adapter` fixture,
adapter regression, generated envelope, Lean receipt, and differential row
cover the admitted forms.

Differential coverage grows **483/477/0/6 → 484/478/0/6**; grammar coverage
remains **235/113/122**. On the checked-in **996-file** SystemVerilog example
sweep (**995 files before this witness**), the adapter census moves **775 clean
/ 220 partial → 786 clean / 210 partial**.

## Pure literal-return function values in the adapter — 2026-10-29

The legacy adapter census now recognizes pure literal-return function calls:
`literal_function_statement`, `literal_function_return`, and
`empty_function_default`. Calls with pure actuals and known literal/default
results carry no callable state; effectful, computed, output-bearing, and
unsupported calls remain loud. The
`pure_literal_function_values_adapter` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the admitted
forms.

Differential coverage grows **482/476/0/6 → 483/477/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 995-file SystemVerilog example
sweep (994 files before this witness), the adapter census moves **766 clean /
228 partial → 775 clean / 220 partial**; `SubroutineSymbol:Subroutine` falls
**14 → 4** and the pure `seven` call residuals fall to zero.

## Discarded pure `$sformatf` calls in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's `sformatf_statement`
marker for discarded literal integral `$sformatf` calls. The formatted value
is unobserved and carries no represented state; dynamic formats, unsupported
conversions, and effectful operands remain loud. The
`pure_sformatf_statements_adapter` fixture, adapter regressions, generated
envelope, Lean receipt, and differential row cover the admitted forms.

Differential coverage grows **481/475/0/6 → 482/476/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 994-file SystemVerilog example
sweep (993 files before this witness), the adapter census moves **765 clean /
228 partial → 766 clean / 228 partial** and the discarded `$sformatf`
residuals fall to zero.

## Discarded pure scalar metadata queries in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's `clog2_statement`,
`isunbounded_statement`, `signing_statement`, and `time_scale_statement`
markers for discarded scalar metadata queries. Constant `$clog2` and
`$isunbounded`, integral signing casts, and timescale metadata carry no
represented state; effectful and value-position forms remain loud. The
`pure_scalar_metadata_statements_adapter` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the admitted
forms.

Differential coverage grows **480/474/0/6 → 481/475/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 993-file SystemVerilog example
sweep (992 files before this witness), the adapter census moves **760 clean /
232 partial → 765 clean / 228 partial** and the six scalar metadata query
residuals fall to zero.

## Discarded pure empty subroutine calls in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's
`empty_subroutine_call` and `empty_input_task_call` markers. Empty tasks and
functions with pure input actuals have no represented state or output, so
their declarations and discarded calls are erased; nonempty, effectful,
output-bearing, and value-position calls remain loud. The
`pure_empty_subroutine_statements_adapter` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the admitted
forms.

Differential coverage grows **479/473/0/6 → 480/474/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 992-file SystemVerilog example
sweep (991 files before this witness), the adapter census moves **757 clean /
234 partial → 760 clean / 232 partial** and the two empty-call declaration
residuals fall to zero.

## Discarded pure type and width queries in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's `typename_statement`
and `bits_statement` markers for discarded `$typename` and `$bits` calls.
Their expression arguments are not evaluated, while malformed and
value-position forms remain loud. The
`pure_type_width_query_statements_adapter` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the admitted
forms.

Differential coverage grows **478/472/0/6 → 479/473/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 991-file SystemVerilog example
sweep (990 files before this witness), the adapter census moves **754 clean /
236 partial → 757 clean / 234 partial** and the two discarded type/width query
residuals fall to zero.

## Discarded pure zero-size queries in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's `zero_size_statement`
marker for discarded `len` and `size` calls on untouched empty string and
queue storage. Initialized, populated, and effectful histories remain loud.
The `pure_zero_size_statements_adapter` fixture, adapter regressions, generated
envelope, Lean receipt, and differential row cover the admitted forms.

Differential coverage grows **477/471/0/6 → 478/472/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 990-file SystemVerilog example
sweep (989 files before this witness), the adapter census moves **752 clean /
237 partial → 754 clean / 236 partial** and the two discarded zero-size query
residuals fall to zero.

## Discarded pure empty associative-array queries in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's
`associative_empty_query_statement` and `associative_empty_endpoint_statement`
markers for discarded `num`, `size`, `first`, and `last` calls on untouched
associative arrays. Populated, dynamic, and effectful histories remain loud.
The `pure_associative_query_statements_adapter` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the admitted
forms.

Differential coverage grows **476/470/0/6 → 477/471/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 989-file SystemVerilog example
sweep (988 files before this witness), the adapter census moves **749 clean /
239 partial → 752 clean / 237 partial** and the four discarded empty
associative-query call residuals fall to zero.

## Discarded pure floating math in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's
`floating_math_statement` marker for discarded source-pure `$sqrt`, `$pow`,
and `$sin` calls. Effectful, timed, unsupported, and value-position forms
remain loud. The `pure_floating_math_statements_adapter` fixture, adapter
regressions, generated envelope, Lean receipt, and differential row cover the
admitted forms.

Differential coverage grows **475/469/0/6 → 476/470/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 988-file SystemVerilog example
sweep (987 files before this witness), the adapter census moves **747 clean /
240 partial → 749 clean / 239 partial** and the three discarded floating-math
call residuals fall to zero.

## Discarded pure enum methods in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's `enum_name_statement`
and `enum_numeric_statement` markers for discarded source-pure enum `name`,
`first`, `last`, `num`, `next`, and `prev` calls. Effectful receivers and step
arguments remain loud. The `pure_enum_method_statements_adapter` fixture,
adapter regressions, generated envelope, Lean receipt, and differential row
cover the admitted forms.

Differential coverage grows **474/468/0/6 → 475/469/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 987-file SystemVerilog example
sweep (986 files before this witness), the adapter census moves **744 clean /
242 partial → 747 clean / 240 partial** and the six discarded enum-method call
residuals fall to zero.

## Discarded pure string queries in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's `string_query_statement`
marker for discarded source-pure `len`, `getc`, `atoi`, `atobin`, `compare`,
and `icompare` calls. Unknown, effectful, and dynamic string histories remain
loud. The `pure_string_query_statements_adapter` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the admitted
forms.

Differential coverage grows **473/467/0/6 → 474/468/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 986-file SystemVerilog example
sweep (985 files before this witness), the adapter census moves **742 clean /
243 partial → 744 clean / 242 partial** and the six discarded string-query
call residuals fall to zero; the separate untouched-empty `len` case remains
on its `zero_size_statement` boundary.

## Discarded pure fixed dimension queries in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's
`dimension_query_statement` marker for discarded fixed packed and unpacked
dimension queries: `$size`, `$high`, `$left`, `$right`, `$low`, `$increment`,
`$dimensions`, and `$unpacked_dimensions`. Dynamic, selected, and effectful
operands remain loud. The `pure_dimension_query_statements_adapter` fixture,
adapter regressions, generated envelope, Lean receipt, and differential row
cover the admitted forms.

Differential coverage grows **472/466/0/6 → 473/467/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 985-file SystemVerilog example
sweep (984 files before this witness), the adapter census moves **740 clean /
244 partial → 742 clean / 243 partial** and the eight discarded dimension-query
call residuals fall to zero.

## Discarded pure fixed-array queries in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's `array_query_statement`
and `array_reduction_statement` markers for discarded fixed-array `min`,
`max`, `unique`, `unique_index`, `sum`, `product`, `and`, `or`, and `xor`
calls, including source-pure `with` clauses. Dynamic or effectful histories
and clauses remain loud. The `pure_array_query_statements_adapter` fixture,
adapter regressions, generated envelope, Lean receipt, and differential row
cover the admitted forms.

Differential coverage grows **471/465/0/6 → 472/466/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 984-file SystemVerilog example
sweep (983 files before this witness), the adapter census moves **736 clean /
247 partial → 740 clean / 244 partial** and the 13 discarded array-query call
residuals fall to zero.

## Discarded pure bit queries in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's `bit_query_statement`
marker for discarded literal and source-pure named-history calls to
`$countbits`, `$countones`, `$onehot`, `$onehot0`, and `$isunknown`. Computed,
dynamic, and effectful operands remain loud. The
`pure_bit_query_statements_adapter` fixture, adapter regressions, generated
envelope, Lean receipt, and differential row cover the admitted forms.

Differential coverage grows **470/464/0/6 → 471/465/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 983-file SystemVerilog example
sweep (982 files before this witness), the adapter census moves **733 clean /
249 partial → 736 clean / 247 partial** and the ten discarded bit-query call
residuals fall to zero.

## Discarded pure real conversions in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's existing source-pure
statement markers for discarded `$itor`, `$bitstoreal`, `$bitstoshortreal`,
`$rtoi`, `$realtobits`, and `$shortrealtobits` conversions. Effectful or
unsupported operands remain loud. The
`pure_real_conversion_statements_adapter` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the admitted
forms.

Differential coverage grows **469/463/0/6 → 470/464/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 982-file SystemVerilog example
sweep (981 files before this witness), the adapter census moves **723 clean /
258 partial → 733 clean / 249 partial** and the 12 discarded-conversion call
residuals fall to zero.

## Existing pure-diagnostic markers in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's existing inert
`pure_diagnostic` markers for monitor toggles, VCD controls, static SDF and
time-format calls, and the null `$system` task. Dynamic or effectful arguments
remain loud. The `pure_diagnostic_markers_adapter` fixture, adapter
regressions, generated envelope, Lean receipt, and differential row cover the
admitted forms.

Differential coverage grows **468/462/0/6 → 469/463/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 943-file SystemVerilog example
sweep, the adapter census moves **688 clean / 254 partial → 698 clean / 245
partial** and the 15 pure-diagnostic call residuals fall to zero.

## Bare assertion-control tasks in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's inert lowering for bare
`$asserton`, `$assertoff`, and `$assertkill` tasks. These assertion controls
carry no represented self-check state; argumented forms remain loud. The
`assertcontrol_tasks_adapter` fixture, adapter regression, generated envelope,
Lean receipt, and differential row cover the admitted shape.

Differential coverage grows **467/461/0/6 → 468/462/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 942-file SystemVerilog example
sweep, the adapter census moves **686 clean / 255 partial → 688 clean / 254
partial** and the three bare assertion-control residuals fall to zero.

## Assertion-control diagnostics in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's inert lowering for
literal and source-pure `$assertcontrol` diagnostics. These controls carry no
self-check assertion state, while dynamic controls remain loud. The
`assertcontrol_adapter` fixture, adapter regressions, generated envelope, Lean
receipt, and differential row cover the admitted shape.

Differential coverage grows **466/460/0/6 → 467/461/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 941-file SystemVerilog example
sweep, `Call:$assertcontrol` residuals fall **3 → 0** (686 clean / 255
partial).

## Unpacked-struct declarations in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's flat-cell lowering for
procedural untagged unpacked structs. A declaration is admitted only when its
conversion produces `Var`/`Empty` cells; unsupported fields and aggregate
boundaries remain loud. The `struct_decl_adapter` fixture, adapter regression,
generated envelope, Lean receipt, and differential row cover the family.

Differential coverage grows **465/459/0/6 → 466/460/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 940-file SystemVerilog example
sweep, `VariableDeclStatement:type` residuals fall **2 → 0** (682 clean /
258 partial).

## Fixed unpacked-array declarations in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's flat-cell lowering for
procedural fixed unpacked arrays. A declaration is admitted only when its
conversion produces `Var`/`Empty` cells; unsupported leaves and aggregate
boundaries remain loud. The `fixed_array_decl_adapter` fixture, adapter
regression, generated envelope, Lean receipt, and differential row cover the
family.

Differential coverage grows **464/458/0/6 → 465/459/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 939-file SystemVerilog example
sweep, `VariableDeclStatement:type` residuals fall **12 → 2** (679 clean /
260 partial).

## Constant-extent dynamic-array declarations in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's finite dynamic-array
lowering. A procedural dynamic-array declaration with a source-pure constant
extent is admitted when the converter produces only flat `Var`/`Empty` cells;
symbolic extents and dynamic target operations remain loud. The
`dynamic_extent_adapter` fixture, adapter regression, generated envelope, Lean
receipt, and differential row cover the family.

Differential coverage grows **463/457/0/6 → 464/458/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 938-file SystemVerilog example
sweep, `VariableDeclStatement:type` residuals fall **20 → 12** (671 clean /
267 partial).

## Invalid packed-dimension declarations in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's compile-time erasure for
malformed integral packed-dimension declarations. Rejected declarations, with
direct literal initializers recovered from their source spelling, allocate no
self-check cells; effectful initializers and value uses remain loud. The
`invalid_dimension_adapter` fixture, adapter regression, generated envelope,
Lean receipt, and differential row cover the family.

Differential coverage grows **462/456/0/6 → 463/457/0/6**; grammar coverage
remains **235/113/122**. The checked-in 937-file SystemVerilog example sweep
remains at **20** `VariableDeclStatement:type` residuals.

## Empty dynamic-array declarations in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's declaration-only path
for zero-size dynamic-array declarations. `new[0]` and empty assignment
patterns create no flat self-check cells, while nonzero allocations and later
value uses remain loud. The `empty_dynamic_decl_adapter` fixture, adapter
regression, generated envelope, Lean receipt, and differential row cover the
family.

Differential coverage grows **461/455/0/6 → 462/456/0/6**; grammar coverage
remains **235/113/122**. The checked-in 936-file SystemVerilog example sweep
remains at **20** `VariableDeclStatement:type` residuals.

## Associative-array declarations in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's static associative-array
declaration erasure. Declarations that the extractor lowers to finite flat
cells or declaration-only storage no longer create a false aggregate type
residual; dynamic keys and value operations remain loud at their existing
boundaries. The `associative_decl_adapter` fixture, adapter regression,
generated envelope, Lean receipt, and differential row cover the family.

Differential coverage grows **460/454/0/6 → 461/455/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 935-file SystemVerilog example
sweep, `VariableDeclStatement:type` residuals fall **23 → 20** while dynamic
associative operations remain loud.

## Mixed-dimension array declarations in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's declaration-only path
for an untouched 2-state array with fixed dimensions around a dynamic
dimension. A declaration such as `bit cells[2][][3]` contributes no flat state
when later code does not read or write its value; initializers and value uses
remain loud. The `mixed_array_dimension_adapter` fixture, adapter regression,
generated envelope, Lean receipt, and differential row cover the family.

Differential coverage grows **459/453/0/6 → 460/454/0/6**; grammar coverage
remains **235/113/122**. The checked-in 934-file SystemVerilog example sweep
remains at **23** `VariableDeclStatement:type` residuals because this exact
declaration shape was not previously present there.

## Literal semaphore declarations in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's literal semaphore
declaration shortcut. A local `semaphore` initialized by a nonnegative literal
`new(N)` contributes no flat declaration state; dynamic constructors and all
semaphore operations remain loud. The `literal_semaphore_adapter` fixture,
adapter regression, generated envelope, Lean receipt, and differential row
cover the family.

Differential coverage grows **458/452/0/6 → 459/453/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 933-file SystemVerilog example
sweep, `VariableDeclStatement:type` residuals fall **24 → 23** while dynamic
object behavior stays loud.

## Opaque class-handle declarations in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's existing erasure of
uninitialized opaque class handles. `mailbox` and `semaphore` declarations in
module and procedural scopes contribute no flat self-check state; handle reads,
construction, assignments, and methods remain loud at their existing
boundaries. The `opaque_handle_adapter` fixture, adapter regression, generated
envelope, Lean receipt, and differential row cover the family.

Differential coverage grows **457/451/0/6 → 458/452/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 932-file SystemVerilog example
sweep, `VariableDeclStatement:type` residuals fall **28 → 24** while the
remaining object, hierarchy, and scheduler boundaries stay loud.

## Clean elaborated generate scopes in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's elaboration flattening
for generate scopes whose generated processes remain in the existing
self-check vocabulary. Generated bodies that contain an unsupported delay or
other boundary remain loud with that nested construct. The `generate_adapter`
fixture, adapter regressions, generated envelope, Lean receipt, and
differential row cover the family.

Differential coverage grows **456/450/0/6 → 457/451/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 931-file SystemVerilog example
sweep, adapter unlockables rise **4 → 5**, while the remaining generate and
hierarchy boundaries stay loud.

## Fixed-array ordering methods in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's assignment-block
lowering for source-pure fixed-array `sort`, `rsort`, and `reverse` calls,
including the existing struct-array ordering path. Unknown, dynamic, and
unsupported array histories remain loud. The `ordering_adapter` fixture,
adapter regressions, generated envelope, Lean receipt, and differential row
cover the family.

Differential coverage grows **455/449/0/6 → 456/450/0/6**; grammar coverage
remains **235/113/122**. The temporary public sv-tests audit remains **380
clean / 421 partial / 111 include skips**; ordering-method adapter residuals
fall to zero in the checked-in ordering fixtures, while unsupported histories
remain loud.

## Severity-task calls in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's represented forms of
`$info`, `$warning`, `$error`, and `$fatal`. Severity calls evaluate their
accepted pure arguments without adding a diagnostic stream to the self-check
state, while `$fatal` retains its represented whole-run halt. Unsupported
argument forms remain loud. The `severity_adapter` fixture, adapter
regressions, generated envelope, Lean receipt, and differential row cover the
family.

Differential coverage grows **454/448/0/6 → 455/449/0/6**; grammar coverage
remains **235/113/122**. The temporary public sv-tests audit remains **380
clean / 421 partial / 111 include skips**; the adapter's severity and fatal
call residuals are removed for the represented forms, while unsupported forms
remain loud.

## Inert pure diagnostics in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's exact inert forms of
`$exit` and `$printtimescale`. These module-originating diagnostics contribute
no represented self-check state; unsupported argument forms and hierarchy
requirements remain loud. The `pure_diagnostic_adapter` fixture, adapter
regressions, generated envelope, Lean receipt, and differential row cover the
admitted shape.

Differential coverage grows **453/447/0/6 → 454/448/0/6**; grammar coverage
remains **235/113/122**. The temporary public sv-tests audit remains **380
clean / 421 partial / 111 include skips**, while adapter residuals
`Call:$exit` fall **1 → 0** and `Call:$printtimescale` fall **2 → 0**;
adapter unlockables remain **7**.

## Source-pure string statement methods in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's source-history erasure
for discarded `string.putc`, `itoa`, `bintoa`, `octtoa`, and `hextoa` calls.
Literal source-pure methods contribute no self-check string state; dynamic,
effectful, and unsupported calls remain loud. The `string_method_adapter`
fixture, adapter regressions, generated envelope, Lean receipt, and
differential row cover the admitted shape.

Differential coverage grows **452/446/0/6 → 453/447/0/6**; grammar coverage
remains **235/113/122**. The temporary public sv-tests audit remains **380
clean / 421 partial / 111 include skips**, while clean-file adapter residuals
`Call:itoa`, `Call:bintoa`, `Call:octtoa`, `Call:hextoa`, and `Call:putc` each
fall **1 → 0**; adapter unlockables remain **7**.

## Empty output arguments — 2026-10-29

Empty arguments in no-conversion `$display` and `$write` calls now lower to
literal spaces through the existing `%s` renderer. Default integral and string
arguments retain their ordinary formatting, while an omitted operand for a
real conversion specifier remains loud. The `empty_display_arguments` fixture,
adapter regressions, generated envelope, Lean receipt, and differential row
cover the family.

Differential coverage grows **451/445/0/6 → 452/446/0/6**; grammar coverage
grows **234/112/122 → 235/113/122**. The temporary public sv-tests audit moves
**368 clean / 433 partial / 111 include skips → 380 / 421 / 111**; the
`EmptyArgumentExpression` adapter residual falls **12 → 0**, and adapter
unlockables remain **7**.

## Unreferenced subroutine metadata — 2026-10-29

The legacy adapter census now mirrors the extractor's identity-based erasure
of uncalled subroutine declarations. An unreferenced task or function has no
time-zero effect and contributes no self-check state; referenced subroutines
remain loud at the callable boundary. The
`unreferenced_subroutine_metadata` fixture, adapter regressions, generated
envelope, Lean receipt, and differential row cover the family.

Differential coverage grows **450/444/0/6 → 451/445/0/6**; grammar coverage
remains **234/112/122**. The temporary public audit remains **368 clean / 433
partial / 111 include skips**, while adapter `SubroutineSymbol:Subroutine`
residuals fall **24 → 22** and the clean `fork_return` residual disappears.

## Resolved forward typedef metadata — 2026-10-29

The legacy adapter census now erases resolved forward typedef declarations
whose matching aliases are already admitted as integral or flat-struct
compile-time metadata. Unresolved, class, and opaque forward declarations
remain loud. The `forward_typedef_metadata` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the admitted
shape.

Differential coverage grows **449/443/0/6 → 450/444/0/6**; grammar coverage
grows **233/111/122 → 234/112/122**. The temporary public sv-tests audit
moves **364 clean / 437 partial / 111 include skips → 368 / 433 / 111**, while
adapter unlockables remain **7**.

## Display format escapes in the adapter — 2026-10-29

The legacy adapter census now treats the first string argument to represented
`$display` and `$write` calls as their format string. Escape spellings are
consumed by the existing formatter before ordinary expression walking, while
dynamic or unsupported value arguments remain loud. The
`display_format_escape_adapter` fixture, adapter regression, generated
envelope, Lean receipt, and differential row cover the admitted shape.

Differential coverage grows **448/442/0/6 → 449/443/0/6**; grammar coverage
remains **233/111/122**. The temporary public sv-tests audit remains **364
clean / 437 partial / 111 include skips**; the clean-file
`StringLiteral:named-control-escape` residual falls **1 → 0**, while adapter
unlockables remain **7**.

## Elaborated bounded `inside` expressions in the adapter — 2026-10-29

The legacy adapter census now supplies the converter's elaborated parameter
scope while walking expressions. Bounded `inside { ... }` membership with
literal or localparam items follows the existing literal membership lowering;
dynamic, effectful, and unsupported forms remain loud. The
`inside_parameter_adapter` fixture, adapter regression, generated envelope,
Lean receipt, and differential row cover the admitted shape.

Differential coverage grows **447/441/0/6 → 448/442/0/6**; the regenerated grammar census is
**233/111/122** (the stale pre-rebase page was **221/112/109**). The
temporary public sv-tests audit remains **364 clean / 437 partial / 111 include
skips**, and adapter unlockables rise **6 → 7**.

## Metadata-only packages in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's package routing for
metadata-only packages. Declaration-only package members, unreferenced
subroutines, and imports contribute no self-check state; package storage and
referenced subroutines remain loud. The `package_metadata` fixture, adapter
regressions, generated envelope, Lean receipt, and differential row cover the
admitted family.

Differential coverage grows **446/440/0/6 → 447/441/0/6**; grammar coverage
remains **221/112/109**. The temporary public sv-tests audit remains **364
clean / 437 partial / 111 include skips**; clean-file `PackageSymbol`
residuals fall from **2 to 0**.

## Compilation-unit typedef metadata in the adapter — 2026-10-29

The legacy adapter census now applies the extractor's declaration-erasure
predicate to compilation-unit members. Integral and flat integral-struct
typedefs, plus bound enum metadata, are compile-time declarations and do not
create self-check state; package storage and unsupported aliases remain loud.
The `compilation_unit_typedef` fixture, adapter regression, generated
envelope, Lean receipt, and differential row cover the family.

Differential coverage grows **445/439/0/6 → 446/440/0/6**; grammar coverage
remains **221/112/109**. The temporary public sv-tests audit remains **364
clean / 437 partial / 111 include skips**; clean-file `TypeAliasType` and
`TransparentMemberSymbol` residuals fall from **26 to 0**.

## Exact integral parameters in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's existing exact integral
parameter path. Elaborated module and compilation-unit parameters contribute
compile-time metadata and bound references, not runtime self-check cells;
real, string, type, and unresolved parameter forms remain loud. The
`parameter_metadata` fixture, adapter regressions, generated envelope, Lean
receipt, and differential row cover the admitted family.

Differential coverage grows **444/438/0/6 → 445/439/0/6**; grammar coverage
remains **221/112/109**. The temporary public sv-tests audit remains **364
clean / 437 partial / 111 include skips**; `ParameterSymbol` residuals fall
from **8 to 0**, while `ParameterSymbol:Parameter` falls from **7 to 6**, with
**3** sole parameter blockers remaining.

## Represented statement calls in the adapter — 2026-10-29

The legacy adapter census now admits the four statement calls whose effects
already have self-check state: `$display`, `$write`, `$finish`, and `$stop`.
Their arguments continue through the existing source-purity checks, while
other system and user calls remain loud at their existing boundaries. The
`statement_call_adapter` fixture, adapter regressions, generated envelope, Lean
receipt, and differential row cover the family.

Differential coverage grows **443/437/0/6 → 444/438/0/6**; grammar coverage
remains **221/112/109**. The temporary public sv-tests audit is unchanged at
**364 clean / 437 partial / 111 include skips**; represented output/termination
calls no longer contribute adapter-only `Call:$stop`/`Call:$write` residuals.

## Local two-state declarations in the adapter — 2026-10-29

The legacy adapter census now uses the extractor's existing integral type
admission for local declarations, including scalar and packed 2-state cells.
Those declarations already lower to static storage or `LocalDecl` with the
ordinary `Squash2` boundary, so the adapter no longer reports a false
`VariableDeclStatement:2state` residual. Unsupported local types and
effectful initializers remain loud. The `local_2state_declarations` fixture,
adapter regressions, generated envelope, Lean receipt, and differential row
cover the admitted family.

Differential coverage grows **442/436/0/6 → 443/437/0/6**; grammar coverage
remains **221/112/109**. The temporary public sv-tests audit is unchanged at
**364 clean / 437 partial / 111 include skips**; its local 2-state declaration
residuals are reduced without changing the extractor classification.

## Compile-time typedef metadata in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's declaration-only path
for integral typedefs, flat integral-struct typedefs, and bound enum metadata.
Those aliases allocate no self-check state, while tagged, generic, and
otherwise unsupported aliases remain loud. The `typedef_metadata` fixture,
adapter regressions, generated envelope, Lean receipt, and differential row
cover the admitted forms.

Differential coverage grows **441/435/0/6 → 442/436/0/6**; grammar coverage
remains **221/112/109**. The temporary public sv-tests audit remains **364
clean / 437 partial / 111 include skips**; the sole compile-time typedef rows
now have no adapter residuals.

## Opaque declaration erasure in the adapter — 2026-10-29

The legacy adapter census now follows the extractor's existing erasure rules
for declaration-only `real`, `realtime`, `shortreal`, `chandle`, and `event`
objects. These objects have no self-check state slot, so their declarations
are omitted while reads, writes, triggers, and waits remain loud at their
existing boundaries. The `opaque_declarations` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the family.

Differential coverage grows **440/434/0/6 → 441/435/0/6**; grammar coverage
grows **220/111/109 → 221/112/109**. The temporary public sv-tests audit
remains **364 clean / 437 partial / 111 include skips**; the sole declaration
rows for these opaque types have no adapter residuals.

## Source-pure string concatenation and replication in the adapter — 2026-10-29

The legacy adapter census now uses the same source-history proof as the
extractor for ASCII string assignments. Literal concatenation and constant
replication can therefore feed later `%s` observations without reporting a
false `VariableSymbol:2state` or `NamedValueExpression:2state` blocker.
Unknown, effectful, timed, and non-ASCII histories remain loud, and no string
storage or scheduler state is added. The `string_concat_replication_ops`
fixture, adapter regressions, generated envelope, Lean receipt, and
differential row cover both §11.4.12.2 forms.

Differential coverage grows **439/433/0/6 → 440/434/0/6**; grammar coverage
remains **111/109**. The temporary public sv-tests audit remains **364 clean /
437 partial / 111 include skips**; the two chapter-11 string rows now have no
adapter residuals.

## Fixed unpacked string-array elements in procedural loops — 2026-10-29

Finite one-dimensional unpacked arrays of ASCII `string` literals now replay
their element values in the legacy self-check tier. Constant reads become the
existing packed literal path; signed integral dynamic indices become an exact
ternary over the declared cells, so `foreach`, `while`, and `do…while` retain
their ordinary loop lowering and string comparisons. Writes, aliases, unequal
cell widths, non-ASCII or dynamic initializers, and aggregate uses remain loud;
the tier adds no string heap or scheduler state. The
`fixed_string_array_loops` fixture, extractor regressions, generated envelope,
and differential row cover the family.

Differential coverage grows **438/432/0/6 → 439/433/0/6**; grammar coverage
remains **111/109**.

## Compilation-unit parameters — 2026-10-29

Compilation-unit `parameter` declarations now lower as elaboration metadata in
the legacy self-check tier. Their bound identities are registered before module
conversion, so references become the same exact constants already used for
module parameters; packed widths may depend on them without creating runtime
cells. Compilation-unit variables and unsupported parameter expression uses
remain loud. The `compilation_unit_parameter` fixture, extractor regression,
generated envelope, Lean receipt, and differential row cover the admitted
family.

Differential coverage grows **437/431/0/6 → 438/432/0/6**; grammar coverage is
unchanged. The external sv-tests-2 checkout is unavailable for a fresh corpus
delta in this item.

## Fixed arrays of initialized unpacked structs — 2026-10-29

Finite fixed unpacked arrays whose leaf is an untagged integral struct now
accept complete positional or keyed element patterns. The extractor flattens
each element into the existing field cells in declared order, retaining the
ordinary 2-state zero and assignment-boundary conversions. Partial,
replicated, effectful, and whole-aggregate forms remain loud because no
aggregate array object is introduced. The `fixed_array_struct_initializer`
fixture, extractor regressions, generated envelope, Lean receipt, and
differential row cover the admitted family.

Differential coverage grows **436/430/0/6 → 437/431/0/6**; grammar coverage is
unchanged. The external sv-tests-2 checkout is unavailable for a fresh corpus
delta in this item.

## Fixed unpacked byte-array string initializers — 2026-10-29

Direct ASCII string literals now initialize finite fixed unpacked byte arrays
in declared index order. A shorter literal supplies zero for the remaining
cells, and the existing flat 2-state cells retain their normal conversion.
Dynamic strings, non-ASCII literals, non-byte element arrays, and aggregate
forms outside this exact conversion remain loud. The
`fixed_array_string_initializer` fixture, extractor regressions, generated
envelope, Lean receipt, and differential row cover the admitted shape.

Differential coverage grows **435/429/0/6 → 436/430/0/6**; grammar coverage is
unchanged. The external sv-tests-2 checkout is unavailable for a fresh corpus
delta in this item.

## Fixed arrays of untagged unions — 2026-10-29

Finite fixed unpacked arrays with an equal-width untagged union leaf now use
one flat aliased vector cell per array element. Selecting either union member
continues to read or write that element's cell, and 2-state cells retain their
zero startup. Tagged, mixed-width, aggregate-initialized, and whole-array
forms remain loud because the legacy state has no aggregate array object. The
`fixed_array_unpacked_union` fixture, extractor regressions, generated
envelope, Lean receipt, and differential row cover the admitted family.

Differential coverage grows **434/428/0/6 → 435/429/0/6**; grammar coverage
is unchanged. The external sv-tests-2 checkout is unavailable for a fresh
corpus delta in this item.

## Dynamic-array and queue dimension queries — 2026-10-29

Direct dynamic arrays and queues now expose source-pure IEEE 1800-2023 §20.7
metadata. Unallocated aggregates report empty bounds, and one constant
`new[N]` dynamic-array allocation reports its current extent; total and
unpacked rank queries remain type metadata. Dynamic allocation sizes, later
mutations, aliases, and aggregate value uses remain loud because the legacy
flat state stores no general container object. The
`dynamic_dimension_queries` fixture, extractor regressions, generated
envelope, Lean receipt, and differential row cover the admitted slice.

Differential coverage grows **433/427/0/6 → 434/428/0/6**; grammar coverage
is unchanged. The fresh all-directory 22,071-file corpus census moves
**5,884 clean / 16,120 partial → 5,901 clean / 16,103 partial** with 67
include skips.

## Mixed fixed and dynamic dimension queries — 2026-10-29

Declaration-only 2-state arrays that combine fixed and dynamic unpacked
dimensions now retain their declared shape for metadata queries. `$size` may
select fixed dimensions around the dynamic slot, while
`$unpacked_dimensions` reports the complete unpacked rank. Selecting the
dynamic dimension, initializing the array, or using its value remains loud
because the legacy flat state has no dynamic storage. The
`mixed_dimension_queries` fixture, extractor regressions, generated envelope,
Lean receipt, and differential row cover the admitted metadata-only slice.

Differential coverage grows **432/426/0/6 → 433/427/0/6**; grammar coverage
remains **220/109/111**.

## Severity-task default formatting — 2026-10-29

The legacy self-check tier now admits `$info`, `$warning`, and `$error` calls
without a format string when their arguments are represented integrals or
source-pure ASCII string histories. The extractor synthesizes `%d`/`%s`
fields, evaluates the pure arguments, and leaves the diagnostic stream outside
the self-check transcript. Opaque and effectful arguments remain loud. The
`severity_default_format` fixture, extractor regressions, generated envelope,
Lean receipt, and differential row cover the new call family. The external
sv-tests-2 snapshot is unchanged because that checkout is unavailable here.

Differential coverage grows **431/425/0/6 → 432/426/0/6**; grammar coverage
remains **220/109/111**.

## Default output formatting — 2026-10-29

The legacy self-check tier now admits `$display` and `$write` calls without a
format string when every argument is a represented integral expression or a
source-pure ASCII string. Integral arguments use the existing decimal
renderer, including the type's default field width and signedness; strings use
the character renderer. Unpacked values, opaque real values, and dynamic
string histories remain loud. The `default_display_format` fixture,
extractor regressions, generated envelope, Lean receipt, and differential row
cover both accepted defaults and the dynamic-string refusal.

The refreshed all-directory 22,516-path census moves **5,965 → 5,968 clean**
and **16,483 → 16,480 partial** (68 include skips). The leading blocker table
is otherwise unchanged because these three newly clean files had no remaining
top-five blocker after the call admission. Differential coverage grows
**430/424/0/6 → 431/425/0/6**; grammar coverage remains **220/109/111**.

## Two-state ordinary wire nets — 2026-10-29

The legacy self-check tier now admits scalar and descending packed `wire bit`
nets. Un-driven cells retain high-impedance net startup; four-state literal
continuous drivers use the existing time-zero lowering and squash `x`/`z` to
zero at the two-state data boundary. Other net kinds, delays, dynamic drivers,
and unsupported shapes remain loud. The `two_state_net` fixture, extractor
regressions, generated envelope, Lean receipt, and differential row cover the
floating and driven cases.

Differential coverage grows **429/423/0/6 → 430/424/0/6**; grammar coverage
remains **220/109/111**.

## Plain user-defined nettypes — 2026-10-29

The legacy self-check tier now lowers an un-driven user-defined nettype with a
four-state integral scalar or packed-vector data type and no resolution
function to a high-impedance flat cell. The nettype declaration is compile-time
metadata; resolution functions, continuous drivers, and unsupported data
shapes remain loud. The `user_nettype` fixture, extractor regressions,
generated envelope, Lean receipt, and differential row cover scalar and vector
observations.

Differential coverage grows **428/422/0/6 → 429/423/0/6**; grammar coverage
grows **219/108/111 → 220/109/111** with a `SyntaxKind.NetTypeDeclaration`
witness.

## Plain un-driven `trireg` nets — 2026-10-29

The legacy self-check tier now lowers a plain, un-driven `trireg` scalar or
packed vector to a declaration-initialized high-impedance flat cell. Charge
strength, delays, declaration drivers, and continuous drivers remain loud
because the envelope has no retained charge or driver state. The `trireg_net`
fixture, extractor regressions, generated envelope, Lean receipt, and
differential row cover the admission and refusal boundaries.

Differential coverage grows **427/421/0/6 → 428/422/0/6**; grammar coverage
remains **219/108/111**.

## Un-driven implicit-pull nets — 2026-10-29

The legacy self-check tier now lowers un-driven `tri0` and `tri1`
declarations to flat cells initialized with their implicit pull zero or one.
Driven forms remain loud because the envelope does not model pull-strength
resolution. The `pull_net` fixture, extractor regressions, generated envelope,
Lean receipt, and differential row cover both values and the driven refusal
boundary.

Differential coverage grows **426/420/0/6 → 427/421/0/6**; grammar coverage
remains **219/108/111**.

## Un-driven wired-resolution nets — 2026-10-29

The legacy self-check tier now lowers un-driven `wand`, `wor`, `triand`, and
`trior` declarations to high-impedance flat cells. Existing literal-driver
resolution remains available; dynamic, strengthened, and unsupported
multi-driver forms remain loud. The `wired_net` fixture, extractor
regressions, generated envelope, Lean receipt, and differential row cover all
four net kinds and a driven refusal boundary.

Differential coverage grows **425/419/0/6 → 426/420/0/6**; grammar coverage
remains **219/108/111**.

## Un-driven `tri` nets — 2026-10-29

The legacy self-check tier now lowers an un-driven `tri` declaration to a
declaration-initialized high-impedance flat cell. Driven nets still use the
existing literal-driver admission or remain loud when strength resolution is
needed. The `tri_net` fixture, extractor regressions, generated envelope, Lean
receipt, and differential row cover scalar/vector high impedance and a driven
refusal boundary.

Differential coverage grows **424/418/0/6 → 425/419/0/6**; grammar coverage
remains **219/108/111**.

## Un-driven supply nets — 2026-10-28

The legacy self-check tier now lowers an un-driven `supply0` or `supply1`
declaration to a declaration-initialized flat cell containing repeated zero or
one bits. Any continuous driver remains loud because the flat state does not
model the IEEE strength lattice or supply-driver identity. The `supply_net`
fixture, extractor regressions, generated envelope, Lean receipt, and
differential row cover both values and the driven refusal boundary.

Differential coverage grows **423/417/0/6 → 424/418/0/6**; grammar coverage
remains **219/108/111**.

## Direct whole-net aliases — 2026-10-28

The legacy self-check tier now admits a module-scope `alias left = right`
when both references are integral nets with equal width and equal four-state
status. All spellings lower to one flat storage cell, so a constant driver
through one name is visible through the other. Selected, concatenated,
non-net, and mismatched aliases remain loud; symbolic `sv-0.2` alias graphs
remain outside this legacy admission.

The `net_alias` fixture, extractor regressions, generated envelope, Lean
receipt, and differential row cover direct and chained aliases plus the
refusal boundaries. Differential coverage grows **422/416/0/6 → 423/417/0/6**;
grammar coverage grows **218/107/111 → 219/108/111**.

## Literal concatenated format strings — 2026-10-28

The legacy self-check output surface folds a concatenation of string literals
used as a `$display`/`$write`/`$strobe`/`$fdisplay`/`$fwrite` or quiet-task
format into the existing output node. Dynamic, integral, and aggregate format
expressions remain loud; no new output or scheduler state is introduced.
The `literal_format_concat` fixture, extractor regressions, generated
envelope, Lean receipt, and differential row cover the admission.

Differential coverage grows **421/415/0/6 → 422/416/0/6**; grammar coverage
remains **218/107/111**.

## Dynamic outer-array assignment targets — 2026-10-28

The legacy self-check tier now lowers blocking assignments through a dynamic
outer unpacked array when the sampled `new[N]` extent is finite and each
element has only fixed unpacked integral dimensions. Dynamic selectors are
expanded to mutually exclusive writes over the existing flattened cells;
constant selectors continue to use the ordinary cell path. Unsampled arrays,
nested dynamic dimensions, aggregate leaves, and effectful or unsupported
forms remain loud. The `nested_dynamic_array_target` fixture, extractor tests,
generated envelope, Lean receipt, and differential row cover the new target
family without adding aggregate storage or scheduler behavior.

Differential coverage grows **419/413/0/6 → 420/414/0/6**; grammar coverage
remains **218/107/111**. The committed external corpus snapshot remains
**5,814 clean / 16,186 partial / 67 include skips** because sv-tests-2 is
unavailable in this worktree; no unverifiable census delta is claimed.

## Fixed-array case-inside widening — 2026-10-28

The legacy self-check tier now admits a fixed unpacked integral array as a
`case (...) inside` label when every cell is no wider than the case subject.
Each cell is converted at the case boundary with the propagated signedness,
then compared through the existing source-order membership chain. Dynamic or
nested arrays, effectful elements, nonintegral storage, and over-wide cells
remain loud. The updated `case_inside/array_widening` receipt and the new
`case_array_widening` fixture provide complete transcripts and a differential
row; no evaluator or scheduler rule changes.

Differential coverage grows **414/408/0/6 → 415/409/0/6**, and grammar coverage
grows **218/102/116 → 218/106/112** as the new fixture supplies the first
witness for several case-item syntax kinds. The committed external corpus
snapshot is **5,814 clean / 16,186 partial / 67 include skips**;
the sv-tests-2 checkout is unavailable in this worktree.

## Pure computed arguments to discarded literal-return functions — 2026-10-28

Discarded calls to source-declared literal-return functions now accept
compile-time pure integral argument expressions, including unary and binary
literal combinations. The function body returns a literal and has only input
formals, so the call has no represented state or scheduler effect. Dynamic,
effectful, named-state, copy-out, and unsupported arguments remain loud. The
`literal_function_computed_statement` fixture, extractor regression, generated
envelope, Lean receipt, and differential row cover the new call-statement
subset.

## Unique0 case labels — 2026-10-28

The legacy self-check tier now lowers ordinary `unique0 case` chains whose
labels are distinct integral literals after whole-case sizing. `unique0` allows
the no-match path, so no `default` is required; the ordinary first-match case
chain therefore preserves both matching and no-match execution. Wildcard,
`inside`, duplicate, dynamic, effectful, and scheduler-facing forms remain
loud. The `unique0_case` fixture, extractor regressions, generated envelope,
Lean receipt, and differential row cover a matching path and an allowed
no-match path without adding overlap-diagnostic or scheduler state.

## Priority case fallbacks — 2026-10-28

The legacy self-check tier now lowers `priority case` and `priority casez`
chains when an explicit `default` covers the qualifier's no-match path. The
existing ordinary case subject, pattern, and first-match lowering supplies the
execution semantics; missing fallbacks, effectful or unsupported expressions,
and scheduler-facing bodies remain loud. The `priority_case_fallback` fixture,
extractor tests, generated envelope, Lean receipt, and differential row cover
the normal and wildcard forms without adding diagnostic state or a scheduler.

## Qualified `if` fallbacks — 2026-10-28

The legacy self-check tier now lowers a qualified `priority if` chain when it
has an explicit final `else`, because every no-match path is covered and the
qualifier adds no observable diagnostic. It also lowers a `unique if` chain only
when each condition is a distinct literal equality over the same integral
variable and the final `else` covers the no-match path, proving that no two
named conditions can overlap. Dynamic, potentially overlapping, qualified, and
missing-fallback forms remain loud; this item adds no diagnostic state or
scheduler behavior. The `qualified_if_fallback` fixture, extractor tests,
generated envelope, Lean receipt, and differential case cover both admitted
forms.

The fresh **22,067-path** census moves **5,794 → 5,804 clean / 16,206 →
16,196 partial / 67 include skips**; `ConditionalStatement:Unique` falls
**20 → 17** and `ConditionalStatement:Priority` falls **11 → 4**. Differential
coverage grows **410/404/0/6 → 411/405/0/6**; grammar coverage remains
**218/101/117**.

## Signed 2-state symbolic declarations — 2026-10-28

The symbolic `sv-0.2` tier now admits signed scalar and packed-vector
declarations when their storage is 2-state. `PDecl.isSigned` survives JSON
ingestion and parameter instantiation alongside `twoState`; signed comparison
operators already emitted by the extractor therefore run through the semantic
tier's two's-complement rule. Signed four-state declarations, enums, arrays,
aggregates, and all scheduler-facing behavior remain loud. The
`symbolic_signed_2state` fixture, extractor regressions, generated envelope,
and Lean receipt cover the metadata and a signed comparison. This symbolic-only
item leaves the self-check differential table and legacy corpus census
unchanged.

## Pure integral-to-real writes — 2026-10-28

The legacy self-check extractor now erases blocking writes from pure integral
expressions into named `real` and `shortreal` storage. Floating storage remains
opaque and floating reads remain loud; source-purity checks keep calls,
increments, member stores, timed writes, and nonblocking publication at the
`AssignmentExpression:target` boundary. The `floating_integral_write` fixture
provides the differential PASS witness, extractor regressions, and Lean receipt.

The fresh **22,067-path** census is **5,794 clean / 16,206 partial / 67 include
skips**, with `AssignmentExpression:target` falling **2,693 → 2,679**.
Differential coverage is **410/404/0/6** and grammar coverage remains
**218/101/117**.

## Source-pure named-string copies — 2026-10-28

Blocking assignments from a named string now sample the source-pure ASCII history at
the assignment point and erase the opaque destination write. The destination keeps
the copied value when the source is subsequently changed; unknown, computed,
timed, nonblocking, and non-ASCII forms remain loud. The
`string_direct_copy` fixture, extractor regressions, sv-tests-2
`6.16--string-assignment-from-literal.sv` receipt, differential row, and Lean
receipt cover the value-copy rule. Differential coverage grows **408 rows / 402
matches / 0 disagreements / 6 recorded refusals → 409 / 403 / 0 / 6**; grammar
coverage remains **218/101/117**. The fresh **22,065-path** census moves **5,790
→ 5,792 clean / 16,208 → 16,206 partial / 67 include skips**;
`CallExpression` falls **2,564 → 2,563** and `NamedValueExpression:2state` falls
**1,269 → 1,267**. The global `AssignmentExpression:target` count remains
**2,693** because these two files also carried other residual blockers in the
previous snapshot.


## Source-pure conditional string assignments — 2026-10-28

A blocking assignment from a conditional string expression now lowers to the
existing opaque-string no-op when its single condition is proven as a source
ordered 0/1 integral literal history and the selected branch is reconstructible
ASCII history. Unknown, computed, pattern, timed, nonblocking, and non-reconstructible
named-string copies remain loud. The `conditional_string_assignment` fixture covers
both branch choices, with extractor regression, differential row, and Lean
receipt.

The fresh **22,067-path** census is **5,792 clean / 16,208 partial / 67 include
skips**, compared with **5,791 / 16,209 / 67** previously;
`AssignmentExpression:target` falls **2,694 → 2,693** and
`NamedValueExpression:2state` falls **1,270 → 1,269**. Differential coverage
grows **407/401/0/6 → 408/402/0/6**; grammar coverage remains **218/101/117**.

## Empty input-only task calls — 2026-10-28

An empty automatic task whose formals are all required `input` values now
lowers to an ordinary `Empty` statement after each actual passes the existing
pure-expression boundary. The declaration is removed from the legacy runtime
view because it has no body, timing, diagnostic, state, or copy-out effect.
Effectful actuals, output/inout/ref or defaulted formals, and nonempty tasks
remain loud. The `empty_input_task` fixture exercises literal and named pure
actuals, with extractor regressions, a differential row, and a Lean receipt.

The fresh **22,067-path** census is **5,791 clean / 16,209 partial / 67 include
skips**, compared with **5,790 / 16,210 / 67** previously;
`ExpressionStatement:CallExpression` falls **2,677 → 2,675** and
`SubroutineSymbol:Subroutine` falls **1,469 → 1,466**, while `CallExpression`
stays at **2,564**. Differential coverage grows **406/400/0/6 → 407/401/0/6**;
grammar coverage changes **218/100/118 → 218/101/117**.

## Automatic static implicit function returns — 2026-10-28

An automatic function with input-only formals and one pure literal assignment
to its implicit scalar return variable now lowers exactly at value and
discarded-call sites. Automatic functions with reads, effects, output formals,
or nonliteral histories remain loud. The
`automatic_implicit_function_return` fixture exercises both an untyped implicit
`logic` return and an explicitly typed automatic return, with extractor
regression, differential row, and Lean receipt.

The fresh **22,067-path** census is **5,790 clean / 16,210 partial / 67 include
skips**, compared with **5,789 / 16,211 / 67** for the previous snapshot;
`CallExpression` falls **2,565 → 2,564**. Differential coverage grows
**405/399/0/6 → 406/400/0/6**; grammar coverage remains **218/100/118**.

## Static implicit function returns — 2026-10-28

A static function with one pure literal assignment to its implicit return
variable now lowers exactly at expression and discarded-statement call sites.
This covers an untyped function's implicit `logic` return and an explicitly
typed function using its implicit variable. Automatic implicit-return functions,
effectful or multi-statement bodies, output formals, and nonliteral histories
remain loud; explicit-return automatic literal functions retain their existing
admission. The `implicit_function_return` fixture exercises both forms, with
extractor regression, differential row, and Lean receipt.

The external sv-tests-2 checkout gained two paths during this measurement: the
fresh **22,067-path** census is **5,789 clean / 16,211 partial** with 67 include
skips, versus **5,785 / 16,213** on the prior 22,065-path snapshot. After
accounting for those external additions, this item moves **5,785 → 5,787 clean**
and **16,213 → 16,211 partial**; `CallExpression` falls **2,567 → 2,565**.
Differential coverage grows **404/398/0/6 → 405/399/0/6**; grammar coverage
remains **218/100/118**.

## Procedural event declarations for pure type queries — 2026-10-28

Procedural `event` declarations now lower to inert metadata in the legacy
self-check state, which has no event-object slot. A pure `$typename(event)`
query therefore returns the exact ASCII spelling `event`; event waits and
triggers remain loud. The `typename_event_declaration` fixture exercises the
query with extractor regression, differential row, and Lean receipt.

The fresh **22,065-path** census moves **5,784 → 5,785 clean** and **16,214 →
16,213 partial** with 67 include skips. `VariableSymbol:2state` falls
**2,105 → 2,101**; `AssignmentExpression:target`,
`ExpressionStatement:CallExpression`, and `CallExpression` remain **2,694**,
**2,677**, and **2,567**. Differential coverage grows **403/397/0/6 →
404/398/0/6**; grammar coverage remains **218/100/118**.

## Scalar string observations after NUL writes — 2026-10-28

Scalar string `.len()` and `.compare()` observations now preserve the exact
ASCII value after an IEEE 1800-2023 §6.16 assignment of integral zero to a
string character. Nonzero indexed writes, dynamic histories, and direct aliases
remain loud. The `string_null_query_observations` fixture exercises both
queries, with extractor regression, differential row, and Lean receipt.

The fresh **22,065-path** census moves **5,782 → 5,784 clean** and **16,216 →
16,214 partial** with 67 include skips. `CallExpression` falls **2,569 →
2,567** while `AssignmentExpression:target` and
`ExpressionStatement:CallExpression` remain **2,694** and **2,677**.
Differential coverage grows **402/396/0/6 → 403/397/0/6**; grammar coverage
remains **218/100/118**.

## Source-pure string queries over concatenations — 2026-10-28

Scalar string observations now replay source-pure concatenation and replication
histories. `.len()`, `.substr()`, and `.compare()` see the exact joined or
repeated ASCII value; dynamic and direct aliased histories remain loud. The
`string_concat_query_observations` fixture exercises both forms, with extractor
regression, differential row, and Lean receipt.

The fresh **22,065-path** census moves **5,779 → 5,782 clean** and **16,219 →
16,216 partial** with 67 include skips. `CallExpression` falls **2,572 →
2,569** while `AssignmentExpression:target` and
`ExpressionStatement:CallExpression` remain **2,694** and **2,677**.
Differential coverage grows **401/395/0/6 → 402/396/0/6**; grammar coverage
remains **218/100/118**.

## Source-pure string compare observations — 2026-10-28

Source-pure literal and query histories now feed exact scalar
`string.compare()` and `string.icompare()` results. Direct named-string aliases,
dynamic or effectful histories, and non-ASCII values remain loud. The
`string_compare_observations` fixture exercises a `$typename` initializer, a
case transform assignment, and both comparison methods, with extractor
regression, differential row, and Lean receipt.

The fresh **22,065-path** census remains **5,779 clean / 16,219 partial** with
67 include skips; `AssignmentExpression:target`,
`ExpressionStatement:CallExpression`, and `CallExpression` remain **2,694**,
**2,677**, and **2,572**. Differential coverage grows **400/394/0/6 →
401/395/0/6**; grammar coverage remains **218/100/118**.

## Source-pure string query observations — 2026-10-28

Direct scalar `.len()` and `.substr()` observations now replay exact ASCII
values from literal and source-pure string query histories. Direct named-string
copies, dynamic or effectful histories, and non-ASCII values remain loud. The
`string_query_observations` fixture exercises both queries on a literal and a
`$typename` history, with extractor regression, differential row, and Lean
receipt.

The fresh **22,065-path** census moves **5,743 → 5,779 clean** and
**16,255 → 16,219 partial** with 67 include skips. `CallExpression` falls
**2,606 → 2,572** and `AssignmentExpression:target` falls **2,695 → 2,694**;
`ExpressionStatement:CallExpression` remains **2,677**. Differential coverage
grows **399/393/0/6 → 400/394/0/6**; grammar coverage remains **218/100/118**.

## Source-pure string query declaration initializers — 2026-10-28

Local string declarations now replay exact ASCII results for source-pure
`toupper()`, `tolower()`, `substr()`, `$sformatf`, and `$typename` query
initializers. The `string_query_initializers` fixture checks case conversion,
substring extraction, and formatting through scalar comparisons. Named copies,
dynamic arguments, effectful histories, and non-ASCII results remain loud.

The fresh **22,065-path** census moves **5,738 → 5,743 clean** and
**16,260 → 16,255 partial** with 67 include skips. `VariableSymbol:2state`
falls **2,112 → 2,105**; `AssignmentExpression:target`,
`ExpressionStatement:CallExpression`, and `CallExpression` remain **2,695**,
**2,677**, and **2,606**. Differential coverage grows **398/392/0/6 →
399/393/0/6**; grammar coverage remains **218/100/118**.

## Source-pure named string concatenation observations — 2026-10-28

The self-check tier now reconstructs source-pure ASCII string values through
multi-operand concatenations for equality and `%s` display. A source-pure
replication of a named string is also replayed exactly, while direct
one-operand packed shells, dynamic, controlled, timed, and non-ASCII histories
remain loud. The `string_concat_comparison` fixture exercises equality and
display, with extractor regression, differential row, and Lean receipt.

The fresh **22,065-path** census moves **5,727 → 5,738 clean** and
**16,271 → 16,260 partial** with 67 include skips. `AssignmentExpression:target`
and `ExpressionStatement:CallExpression` remain **2,695** and **2,677**;
`CallExpression` remains **2,606**, while `NamedValueExpression:2state` falls
**1,293 → 1,269**. Differential coverage grows **397/391/0/6 →
398/392/0/6**; grammar coverage remains **218/100/118**.

## `$typename` string comparisons — 2026-10-28

The self-check tier now lowers source-pure `$typename` queries to ASCII packed
strings. Direct comparisons and blocking assignments followed by `.len()` use
the frontend's resolved type spelling; effectful or non-ASCII sources remain
loud. The `typename_comparison` fixture exercises both forms, with extractor
regression, differential row, and Lean receipt.

The fresh **22,065-path** census moves **5,723 → 5,727 clean** and
**16,275 → 16,271 partial** with 67 include skips. `CallExpression` falls
**2,613 → 2,606**; the top `AssignmentExpression:target` and
`ExpressionStatement:CallExpression` blockers remain **2,695** and **2,677**.
Differential coverage grows **396/390/0/6 → 397/391/0/6**; grammar coverage
remains **218/100/118**.

## String case-conversion comparisons — 2026-10-28

The self-check tier now compares source-pure literal-history
`string.toupper()` and `string.tolower()` results with exact ASCII string
operands. IEEE 1800-2023 §§6.16.4–6.16.5 leave nonalphabetic characters
unchanged, which the `string_case_comparison` fixture exercises alongside
both case transformations. Dynamic, controlled, timed, and non-ASCII histories
remain loud; the extractor regression and Lean receipt pass.

The fresh **22,065-path** census moves **5,719 → 5,723 clean** and
**16,279 → 16,275 partial** with 67 include skips. `CallExpression` falls
**2,617 → 2,613**; the top `AssignmentExpression:target` and
`ExpressionStatement:CallExpression` blockers remain **2,695** and **2,677**.
Differential coverage grows **395/389/0/6 → 396/390/0/6**; grammar coverage
remains **218/100/118**.

## Enum `.name()` comparisons — 2026-10-28

The self-check tier now preserves the packed bytes of ASCII string literals
through slang's propagated conversion to `string`, so equality expressions can
compare them with declaration-order `enum.name()` results. Direct names,
`first()`/`last()` chains, and the empty result for invalid values are covered
by the `enum_name_comparison` fixture, extractor regression, and Lean receipt;
dynamic string storage and symbolic-mode enum calls remain loud.

The fresh **22,065-path** census moves **5,703 → 5,719 clean** and
**16,295 → 16,279 partial** with 67 include skips. The top
`AssignmentExpression:target`, `ExpressionStatement:CallExpression`, and
`CallExpression` blockers remain **2,695**, **2,677**, and **2,617**.
Differential coverage grows **394/388/0/6 → 395/389/0/6**; grammar coverage
remains **218/100/118**.

## Context-sized associative-array `exists` comparisons — 2026-10-28

The self-check tier now admits finite literal-key associative-array
`exists(index)` results in equality and case-equality expressions. IEEE
1800-2023 §7.9.3 returns an unsigned one-bit presence result, and equality
context sizing zero-extends it to the larger operand width before comparison.
Dynamic keys, aliases, and aggregate histories remain loud. The
`assoc_exists_sized_comparison` fixture, extractor regression, and Lean receipt
pass.

The fresh **22,065-path** census moves **5,699 → 5,703 clean** and
**16,299 → 16,295 partial** with 67 include skips. The four
`BinaryExpression:width` blockers are removed; the top
`AssignmentExpression:target`, `ExpressionStatement:CallExpression`, and
`CallExpression` counts remain **2,695**, **2,677**, and **2,617**.
Differential coverage grows **393/387/0/6 → 394/388/0/6**; grammar coverage
remains **218/100/118**.

## Unsigned packed integral associative-array endpoints — 2026-10-28

The self-check tier now admits source-pure finite associative arrays whose
integral index is an unsigned packed alias. IEEE 1800-2023 §7.8.4 orders keys
according to that index type's signedness, so `first` and `last` select `0` and
`15` from the keys `0`, `8`, and `15`. Dynamic keys, controls, timing, and
aggregate forms remain loud. The `assoc_unsigned_endpoint_history` fixture,
extractor regression, and Lean receipt pass.

The fresh **22,065-path** census moves **5,698 → 5,699 clean** and
**16,300 → 16,299 partial** with 67 include skips.
`ExpressionStatement:CallExpression` falls **2,678 → 2,677**;
`AssignmentExpression:target` remains **2,695** and `CallExpression` remains
**2,617**. Differential coverage grows **392/386/0/6 → 393/387/0/6**;
grammar coverage remains **218/100/118**.

## `string.putc` at the string length — 2026-10-28

The self-check tier now admits the source-pure `s.putc(s.len(), "X")` form.
IEEE 1800-2023 §6.16.2 defines an index equal to the current string length as
out of range, so the literal string history remains unchanged. Dynamic or
aliased length expressions, controls, timing, and non-ASCII values remain
loud. The `string_putc_length_index` fixture, extractor regression, and Lean
receipt pass.

The fresh **22,065-path** census moves **5,697 → 5,698 clean** and
**16,301 → 16,300 partial** with 67 include skips.
`ExpressionStatement:CallExpression` falls **2,679 → 2,678**;
`AssignmentExpression:target` remains **2,695** and `CallExpression` remains
**2,617**. Differential coverage grows **391/385/0/6 → 392/386/0/6**;
grammar coverage remains **218/100/118**.

## Scalar string integer-conversion histories — 2026-10-28

The self-check tier now replays source-pure `itoa`, `bintoa`, `octtoa`, and
`hextoa` calls on opaque strings. Literal integral arguments replace the string
with exact unpadded ASCII decimal, binary, octal, or lower-case hexadecimal
text, including signed decimal/base renderings. Dynamic arguments, unknown
values, aliases, control-dependent calls, and unsupported signatures remain
loud. The `string_integer_conversion` fixture, extractor regressions, and Lean
receipt pass.

The fresh **22,065-path** census moves **5,684 → 5,697 clean** and
**16,314 → 16,301 partial** with 67 include skips. The
`ExpressionStatement:CallExpression` blocker falls **2,694 → 2,679**;
`AssignmentExpression:target` remains **2,695** and `CallExpression` remains
**2,617**. Differential coverage grows **390/384/0/6 → 391/385/0/6**; grammar
coverage remains **218/100/118**.

## Discarded finite associative-array `exists` — 2026-10-28

The self-check tier now erases a discarded `exists(index)` call when the
receiver is a finite literal-key associative array represented by flat value
and presence cells. The result is a pure one-bit observation and has no
represented state effect. Dynamic keys, aliases, controls, timing, and other
aggregate uses remain loud. The `assoc_exists_statement` fixture, extractor
regressions, and Lean receipt pass.

The fresh **22,065-path** census remains **5,684 clean** and **16,314
partial** with 67 include skips; the top `AssignmentExpression:target`,
`ExpressionStatement:CallExpression`, and `CallExpression` counts remain
**2,695**, **2,694**, and **2,617**. Differential coverage grows **389/383/0/6
→ 390/384/0/6**; grammar coverage remains **218/100/118**.

## Empty associative-array low/high bounds — 2026-10-28

Untouched integral-key associative arrays now lower `$low` and `$high` as
all-`x` index results, as required by IEEE 1800-2023 §20.7. The result composes
with `$isunknown` and the exact zero `$size` query. Populated, dynamic, aliased,
controlled, and timed histories remain loud. The
`assoc_system_empty_bounds_history` fixture, extractor regression, and Lean
receipt pass.

The fresh **22,065-path** census moves **5,681 → 5,684 clean** and
**16,317 → 16,314 partial** with 67 include skips. The
`CallExpression:dimension:argument` blocker falls **37 → 34**; the top
`AssignmentExpression:target` and `ExpressionStatement:CallExpression`
counts remain **2,695** and **2,694**. Differential coverage grows
**388/382/0/6 → 389/383/0/6**.

## System associative-array dimension bounds — 2026-10-28

System queries `$left`, `$right`, `$low`, `$high`, `$increment`, and `$size`
now observe source-pure finite integral-key associative-array histories. The
flat presence replay returns the populated low/high keys, fixed integral-index
metadata, and exact count after literal writes, compound writes, and `delete`.
Dynamic selectors, aliases, controls, timing, string-key arrays, and empty
`$low`/`$high` unknown-result cases remain loud. The
`assoc_system_bounds_history` fixture, extractor regression, and Lean receipt
pass.

The fresh **22,065-path** census moves **5,674 → 5,681 clean** and
**16,324 → 16,317 partial** with 67 include skips. `AssignmentExpression:target`
falls **2,702 → 2,695**, `ExpressionStatement:CallExpression` falls
**2,695 → 2,694**, and `CallExpression` remains **2,617**. The
`CallExpression:dimension:argument` blocker falls **44 → 37**. Differential
coverage grows **387/381/0/6 → 388/382/0/6**.

## System `$size` on finite associative-array histories — 2026-10-28

The self-check tier now routes `$size` on a source-pure finite integral-key
associative array through the existing presence replay. It returns the exact
allocated-key count across literal writes, compound writes, and `delete`,
including zero for an untouched or cleared array. Fixed-array `$size` keeps its
declared-dimension path; string-key arrays, dynamic selectors, aliases,
controls, and timing remain loud. The `assoc_system_size_history` fixture,
extractor regression, and Lean receipt pass.

The fresh **22,065-path** census moves **5,670 → 5,674 clean** and
**16,328 → 16,324 partial** with 67 include skips. `AssignmentExpression:target`
falls **2,706 → 2,702**, `ExpressionStatement:CallExpression` falls
**2,696 → 2,695**, and `CallExpression` remains **2,617**. The
`CallExpression:dimension:argument` blocker falls **48 → 44**. Differential
coverage grows **386/380/0/6 → 387/381/0/6**; grammar coverage moves
**218/100/118 → 218/101/117**.

## Finite associative-array compound assignment histories — 2026-10-28

Source-pure finite associative arrays now admit IEEE 1800-2023 §10.4.1
compound assignments (`+=`, `<<=`, and the other ordinary arithmetic and bit
operators) at literal selectors or immutable literal-key bindings. The
existing flat-cell lowering captures the selected value and marks presence;
`num()` and `size()` replay those writes and report the exact distinct-key
count. Dynamic selectors, aliases, controls, timing, and unsupported operators
remain loud. The `assoc_compound_history` fixture, extractor regressions, and
Lean receipt pass.

The fresh **22,065-path** census moves **5,668 → 5,670 clean** and
**16,330 → 16,328 partial** with 67 include skips. The
`AssignmentExpression:target` blocker remains **2,706**,
`ExpressionStatement:CallExpression` remains **2,696**, and `CallExpression`
falls **2,619 → 2,617**. Differential coverage grows **385/379/0/6 →
386/380/0/6**; grammar coverage moves **218/99/119 → 218/100/118**.

## Finite associative-array `next()`/`prev()` histories — 2026-10-28

Integral-key finite associative arrays now lower `next(index)` and
`prev(index)` in source-pure histories. The result is one and the index moves
to the nearest present key strictly above or below its input; a failed lookup
returns zero and leaves the index unchanged. Dynamic keys, string outputs,
aliases, and timed or control-dependent histories remain loud. The
`assoc_next_prev_history` fixture, extractor regressions, and Lean receipt
pass.

The fresh **22,065-path** census moves **5,661 → 5,668 clean** and
**16,337 → 16,330 partial** with 67 include skips. The
`AssignmentExpression:target` blocker falls **2,721 → 2,706**,
`ExpressionStatement:CallExpression` falls **2,700 → 2,696**, and
`CallExpression` falls **2,624 → 2,619**. Differential coverage grows
**384/378/0/6 → 385/379/0/6**, and grammar coverage remains **218/97/121**.

## Sorted finite associative-array streaming — 2026-10-28

Right streaming now admits a finite integral-key associative array whose
observed keys and values are source-pure literals. The flat lowering expands
one scalar cell per key in ascending index order, matching IEEE 1800-2023
§11.4.14.1; dynamic keys, non-integral aggregates, and other whole-array uses
remain loud. The `streaming_assoc_sorted` fixture, extractor regressions, and
Lean receipt pass.

The fresh **22,065-path** census moves **5,646 → 5,661 clean** and
**16,352 → 16,337 partial** with 67 include skips. The
`AssignmentExpression:target` blocker falls **2,744 → 2,721**,
`ExpressionStatement:CallExpression` falls **2,710 → 2,700**, and
`CallExpression` falls **2,635 → 2,624**. Differential coverage grows
**383/377/0/6 → 384/378/0/6**, and grammar coverage remains **218/97/121**.

## Discarded finite associative-array endpoint histories — 2026-10-28

Discarded integral-key associative-array `first(index)` and `last(index)`
calls now preserve their output-index side effect through the same presence
priority chain as value assignments. Empty arrays leave the index unchanged;
string-key outputs and dynamic histories remain loud. The
`assoc_endpoint_statement_history` fixture and Lean receipt pass.

The committed 22,065-path census remains **5,646 clean / 16,352 partial** with
67 include skips; `AssignmentExpression:target` remains **2,744**,
`ExpressionStatement:CallExpression` **2,710**, and `CallExpression` **2,635**.
Differential coverage grows **382/376/0/6 → 383/377/0/6**, and grammar coverage
remains **218/97/121**.

## Finite associative-array `first()`/`last()` histories — 2026-10-28

Blocking assignments from integral-key associative-array `first(index)` and
`last(index)` now lower to a presence-priority chain. They return one and
update the index variable to the least or greatest present literal key; an
empty array returns zero and leaves the index unchanged. String-key endpoint
outputs and dynamic or unsupported histories remain loud. The
`assoc_endpoint_history` fixture and Lean receipt pass.

The committed 22,065-path census remains **5,646 clean / 16,352 partial** with
67 include skips; `AssignmentExpression:target` remains **2,744**,
`ExpressionStatement:CallExpression` **2,710**, and `CallExpression` **2,635**.
Differential coverage grows **381/375/0/6 → 382/376/0/6**, and grammar coverage
remains **218/97/121**.

## Finite associative-array delete histories — 2026-10-28

Blocking `delete(key)` and whole-array `delete()` calls now replay through
finite literal-key associative-array history. A key delete restores the
element default and clears its presence bit; a whole-array delete clears every
known cell, so later `exists`, element reads, and `num()`/`size()` observations
see the deletion. Dynamic keys, aliases, timed/control-dependent calls, and
unknown aggregate operations remain loud. The `assoc_delete_history` fixture
and Lean receipt pass.

The committed 22,065-path census remains **5,646 clean / 16,352 partial** with
67 include skips; `AssignmentExpression:target` remains **2,744**,
`ExpressionStatement:CallExpression` **2,710**, and `CallExpression` **2,635**.
Differential coverage grows **380/374/0/6 → 381/375/0/6**, and grammar coverage
remains **218/97/121**.

## Finite associative-array `num()`/`size()` histories — 2026-10-28

Blocking `num()` and `size()` queries on source-pure associative arrays now
replay the number of distinct literal integral or ASCII string keys written
before the query. Repeated writes do not increase the count. Dynamic keys,
aliases, deletes, whole-array operations, timed/control-dependent writes, and
other aggregate methods remain loud. The `assoc_count_history` fixture and
Lean receipt pass.

The fresh 22,065-path census moves **5,637 → 5,646 clean / 16,361 → 16,352
partial** with 67 include skips; `AssignmentExpression:target` falls
**2,751 → 2,744**, `ExpressionStatement:CallExpression` remains **2,710**, and
`CallExpression` falls **2,645 → 2,635**. Differential coverage grows
**379/373/0/6 → 380/374/0/6**, and grammar coverage remains **218/97/121**.

## Source-pure `string.putc` history — 2026-10-28

Blocking `string.putc(index, character)` calls now replay through the existing
ASCII string history. Constant indices and one-byte ASCII or literal integral
characters are admitted, including IEEE low-byte conversion; zero, negative,
and out-of-range writes leave the value unchanged. Dynamic indices or
characters, timed or control-dependent calls, aliases, and non-ASCII values
remain loud. The `string_putc_history` fixture and Lean receipt pass.

The fresh 22,065-path census moves **5,629 → 5,637 clean / 16,369 → 16,361
partial** with 67 include skips; `ExpressionStatement:CallExpression` falls
**2,722 → 2,710**, while `AssignmentExpression:target` remains **2,751**.
Differential coverage grows **378/372/0/6 → 379/373/0/6**, and grammar coverage
remains **218/97/121**.

**Status: the workstream's founding document.** The owner chartered the
language-family programme with *"System Verilog also has a spec, that we
can similarly follow"* — versioned surfaces, spec-mirror as the general
behaviour — and this charter founds the SV lane on the C tier's proven
template (`docs/c-tier-charter.md`, §L35): census first, corpus and
licence surveyed per-file, taxonomy mapped, first milestone planned.
**No Lean semantics in this pass. No existing file changed** by the
charter itself; the consolidation commit that followed it is listed in
§10.

**It presented six decisions and recommended none. The owner ruled all
six the same day** — §6 records them verbatim, §8 re-cuts the ladder
around them, and §9 lists the one thing still outstanding, which is an
access rather than a decision.

---

## Wrapped top-level `$sformatf("%m")` string assignments — 2026-10-28

Blocking assignments from literal text wrapped around the metadata-only
top-level `$sformatf("%m")` query now replay through source-pure string history.
Nested hierarchy, functions, generated scopes, dynamic formats, timed writes,
and nonblocking publication remain loud. The
`string_sformatf_scope_wrapper_assignment` fixture and Lean receipt pass;
differential coverage grows **377/371/0/6 → 378/372/0/6**. The committed
22,065-path census remains **5,622 clean / 16,376 partial** with 67 include
skips and `AssignmentExpression:target` at **2,757**.

## Top-level `$sformatf("%m")` string assignments — 2026-10-28

Blocking assignments from the metadata-only top-level `$sformatf("%m")` query
now replay the module scope through source-pure string history. Nested
hierarchy, functions, generated scopes, and other dynamic format forms remain
loud. The `string_sformatf_scope_assignment` fixture and Lean receipt pass;
differential coverage grows **376/370/0/6 → 377/371/0/6**. The committed
22,065-path census remains **5,622 clean / 16,376 partial** with 67 include
skips and `AssignmentExpression:target` at **2,757**.

## Metadata-only `$typename` string assignments — 2026-10-28

Blocking assignments of `$typename` results now replay the resolved ASCII
type spelling through the source-pure string history. Data-type and named-value
queries are admitted; effectful, dynamic, timed, and nonblocking forms remain
loud. The `string_typename_assignment` fixture and Lean receipt pass, and the
differential matrix grows **375/369/0/6 → 376/370/0/6**. The fresh corpus
census moves **5,611 → 5,622 clean / 16,387 → 16,376 partial** and lowers the
`AssignmentExpression:target` wall **2,782 → 2,757**.

## 2026-10-09 RESTART — surface and kernel ownership

The lane resumes against `e565769`. The dated measurements below are
historical evidence, not today's coverage: `LeanModels/Sv/` now contains
**22 Lean files and 9 950 lines**, and `LeanModels.lean` imports the SV
tests, symbolic ingestion, and scheduler chain. The original claim that
the umbrella does not build the tier no longer describes the tree.

The surface lane owns clauses 5–8, 10–13, 20–26 and the extractor and
differential harness. The kernel lane owns clause 4 scheduling and
clause 9 processes, including event/update queues, nonblocking
assignments, completion, forks and named events. Surface constructs
compile to that kernel's rules; missing rules are requests to the kernel
lane, never a second scheduler. The R1-before-breadth dependency in §8
remains, but kernel and independent surface work have separate owners.

The fixture census's `clean` classification means only that the elaborated
M0 envelope has no `Unsupported` nodes: it does not establish Lean
admission, simulator agreement, valid elaboration, or live execution.
The symbolic `sv-0.2` tier requires its own coverage measurement.

## Multidimensional fixed-array subarray copies — 2026-10-28

A constant subarray reference such as `source[1]` now lowers into a
multidimensional fixed unpacked integral destination by pairing ordinal leaf
cells. Same-root overlap, dynamic selections, and effectful sources remain
loud because they need a source snapshot or aggregate storage. The
`fixed_array_nested_subarray_copy` fixture and Lean receipt supply the `PASS`
evidence; differential coverage grows **374/368/0/6 → 375/369/0/6**.

## Multidimensional fixed-array conditional self-aliases — 2026-10-28

A blocking conditional assignment over a multidimensional fixed unpacked
integral array now lowers each ordinal cell to a source-preserving ternary,
including differing declared bounds with equal shapes. Nonblocking self-alias
branches remain loud because publication is scheduler-visible. The
`fixed_array_nested_conditional_self_alias` fixture and Lean receipt supply the
`PASS` evidence; differential coverage grows **373/367/0/6 → 374/368/0/6**.

## Multidimensional fixed-array self-copies — 2026-10-28

An exact blocking self-copy of a multidimensional fixed unpacked integral array
now lowers to the existing flattened-cell `Empty` path. Nonblocking, partial,
dynamic, and effectful copies remain loud because their publication or storage
semantics are not represented. The `fixed_array_nested_self_copy` fixture and
Lean receipt supply the `PASS` evidence; differential coverage grows
**372/366/0/6 → 373/367/0/6**.

## Conditional fixed-array self-aliases — 2026-10-28

A blocking whole-array conditional assignment may read the destination in one
branch; each fixed-array cell now lowers to a source-preserving ternary.
Nonblocking self-alias branches remain loud because publication is
scheduler-visible. The `fixed_array_conditional_self_alias` fixture and Lean
receipt supply the `PASS` evidence; differential coverage grows **371/365/0/6
→ 372/366/0/6**.

## Conditional unpacked-struct self-aliases — 2026-10-28

A blocking whole-struct conditional assignment may read the destination in one
branch; each integral field now lowers to a source-preserving ternary.
Nonblocking self-alias branches remain loud because publication is
scheduler-visible. The `unpacked_struct_conditional_self_alias` fixture and
Lean receipt supply the `PASS` evidence; differential coverage grows
**370/364/0/6 → 371/365/0/6**.

## Unpacked-struct self-copies — 2026-10-28

An exact blocking self-copy of a flattened integral unpacked struct now lowers
to the existing flat-cell `Empty` path. Nonblocking self-copies remain loud
because their publication is scheduler-visible. The
`unpacked_struct_self_copy` fixture and Lean receipt supply the `PASS`
evidence; differential coverage grows **369/363/0/6 → 370/364/0/6**.

## Fixed-array unpacked-struct self-copies — 2026-10-28

An exact blocking self-copy of a one-dimensional fixed unpacked array of
integral unpacked structs now lowers to the existing flat-cell `Empty` path.
Nonblocking self-copies remain loud because their publication is
scheduler-visible. The `fixed_array_struct_self_copy` fixture and Lean receipt
supply the `PASS` evidence; differential coverage grows **368/362/0/6 →
369/363/0/6**.

## Multiple integral `$sformatf` string assignments — 2026-10-28

Blocking assignments from `$sformatf` forms with at least two integral
conversions and literal ASCII text now use the source-pure string-history path
for known integral literals. Dynamic or nested operands, unsupported markers,
timed forms, and nonblocking writes remain loud. The
`string_sformatf_multiple_integral_assignment` fixture and Lean receipt supply
the `PASS` evidence; differential coverage grows **367/361/0/6 → 368/362/0/6**.

## Escaped-percent integral `$sformatf` string assignments — 2026-10-28

Blocking assignments from `$sformatf` forms with one escaped percent (`%%`),
one integral conversion, and literal ASCII text now use the source-pure
string-history path for known literals. Multiple conversions or escaped
percents, dynamic operands, timed forms, and nonblocking writes remain loud.
The `string_sformatf_percent_literal_assignment` fixture and Lean receipt
supply the `PASS` evidence; differential coverage grows **366/360/0/6 →
367/361/0/6**.

## Integral ASCII-code `$sformatf` string assignments — 2026-10-28

Blocking assignments from `%s`/`%S` `$sformatf` forms now use the source-pure
string-history path for known integral literals whose packed bytes are all
printable ASCII. Unknown, non-byte-width, NUL/control, dynamic, timed, and
nonblocking forms remain loud. The `string_sformatf_ascii_codes_assignment`
fixture and Lean receipt supply the `PASS` evidence; differential coverage
grows **365/359/0/6 → 366/360/0/6**.

## Literal-prefix/suffix integral `$sformatf` assignments — 2026-10-28

Blocking assignments from `$sformatf` forms with one integral conversion and
literal ASCII text around it now use the source-pure string-history path for
known literals. Decimal, hexadecimal, binary, octal, and character forms are
covered; dynamic operands, multiple conversions, escaped-percent formats,
timed forms, and nonblocking writes remain loud. The
`string_sformatf_integral_wrapper_assignment` fixture and Lean receipt supply
the `PASS` evidence; differential coverage grows **364/358/0/6 → 365/359/0/6**.

## Zero-width string `$sformatf` assignments — 2026-10-28

Blocking assignments from `%0s`/`%0S` `$sformatf` forms now use the existing
source-pure ASCII string-history path, including a single literal prefix and
suffix around the conversion. Dynamic or non-ASCII operands, additional
conversions, timed forms, and nonblocking writes remain loud. The
`string_sformatf_zero_width_string_assignment` fixture and Lean receipt supply
the `PASS` evidence; differential coverage grows **363/357/0/6 → 364/358/0/6**.

## Zero-width binary and octal `$sformatf` string assignments — 2026-10-28

Blocking assignments from `%0b/%0B` and `%0o/%0O` `$sformatf` forms now use the
existing source-history path for known 0/1 integral literals, stripping binary
leading zeroes and retaining minimal octal text. Unknown or dynamic operands,
timed forms, and nonblocking writes remain loud. The
`string_sformatf_zero_width_assignment` fixture and Lean receipt supply the
`PASS` evidence; differential coverage grows **362/356/0/6 → 363/357/0/6**.

## Literal decimal `$sformatf` string assignments — 2026-10-28

Blocking assignments from decimal `$sformatf` forms (`%d`, `%D`, `%0d`, and
`%0D`) now use the existing source-history path for known integral literals.
Unknown or dynamic operands, timed forms, and nonblocking writes remain loud.
The `string_sformatf_decimal_assignment` fixture and Lean receipt supply the
`PASS` evidence; differential coverage grows **361/355/0/6 → 362/356/0/6**.

## Literal octal `$sformatf` string assignments — 2026-10-28

Blocking assignments from `$sformatf("%o", ...)` and `$sformatf("%O", ...)` now
use the existing source-history path for known 0/1 integral literals, retaining
the exact lower-case octal text. Unknown or dynamic operands, timed forms, and
nonblocking writes remain loud. The `string_sformatf_octal_assignment` fixture
and Lean receipt supply the `PASS` evidence; differential coverage grows
**360/354/0/6 → 361/355/0/6**.

## Literal binary `$sformatf` string assignments — 2026-10-28

Blocking assignments from `$sformatf("%b", ...)` and `$sformatf("%B", ...)` now
use the existing source-history path for known 0/1 integral literals, retaining
the literal's packed width. Unknown or dynamic operands, timed forms, and
nonblocking writes remain loud. The `string_sformatf_binary_assignment` fixture
and Lean receipt supply the `PASS` evidence; differential coverage grows
**359/353/0/6 → 360/354/0/6**.

## Literal character `$sformatf` string assignments — 2026-10-28

Blocking assignments from `$sformatf("%c", ...)` and `$sformatf("%C", ...)` now
use the existing ASCII source-history path for known integral literals. Unknown,
zero, non-ASCII/control, dynamic, timed, and nonblocking forms remain loud. The
`string_sformatf_char_assignment` fixture and Lean receipt supply the `PASS`
evidence; differential coverage grows **358/352/0/6 → 359/353/0/6**.

## Source-pure string `$sformatf` assignments — 2026-10-28

Blocking assignments from `$sformatf("%s", ...)` and `$sformatf("%S", ...)` now
use the existing source-pure ASCII string-history path when the operand is a
literal or an earlier direct ASCII string history. Dynamic operands,
unsupported formats, timed forms, and nonblocking writes remain loud. The
`string_sformatf_string_assignment` fixture and Lean receipt supply the
`PASS` evidence; differential coverage grows **357/351/0/6 → 358/352/0/6**.

## Literal `$sformatf` string assignments — 2026-10-28

The existing literal formatter now supplies source-pure ASCII history for
blocking string assignments of `%h`/`%H` results from integral literals. Later
string comparisons and diagnostics observe the exact hexadecimal text;
dynamic operands, other formats, timed forms, and nonblocking writes remain
loud. The `string_sformatf_literal_assignment` fixture supplies the `PASS`
differential row and Lean receipt.

The fresh census moves **5,582 → 5,584 clean / 16,416 → 16,414 partial** with
67 include skips, and `AssignmentExpression:target` falls **2,812 → 2,810**.
Differential coverage grows **356/350/0/6 → 357/351/0/6**; grammar coverage
remains **218/97/121**.

## Literal string-index character assignments — 2026-10-28

IEEE 1800-2023 §6.16 permits a constant-index string byte to receive a
one-byte ASCII literal. The legacy extractor now replays direct literal whole
string and byte histories in source order, preserving later comparisons and
`%0s` diagnostics while leaving dynamic, out-of-range, multi-byte, timed, and
nonblocking writes loud. The `string_index_literal_character` fixture supplies
the `PASS` differential row and Lean receipt.

The fresh census moves **5,580 → 5,582 clean / 16,418 → 16,416 partial** with
67 include skips, and `AssignmentExpression:target` falls **2,814 → 2,812**.
Differential coverage grows **355/349/0/6 → 356/350/0/6**; grammar coverage
remains **218/97/121**.

## NUL string-literal character assignments — 2026-10-28

IEEE 1800-2023 §6.16 says a string cannot contain the special NUL character,
so a blocking `s[i] = "\\0"` write is ignored just like `s[i] = 0`. The
legacy self-check extractor now admits the literal form for a constant index
while retaining the existing loud boundary for dynamic, nonzero, timed, and
nonblocking writes. The `string_null_literal_character` fixture supplies the
`PASS` differential row and Lean receipt.

The corpus census moves **5,579 → 5,580 clean / 16,419 → 16,418 partial**
with 67 include skips, and `AssignmentExpression:target` falls
**2,815 → 2,814**. Differential coverage grows **354/348/0/6 → 355/349/0/6**;
grammar coverage remains **218/97/121**.

## Literal queue write followed by empty concatenation — 2026-10-28

A blocking literal queue write followed by an empty queue concatenation is now
admitted when the only later observation is `.size()`. The earlier opaque
write is erased because the empty assignment replaces it before the query;
dynamic or nonliteral writes, element reads, pushes, and other observations
remain loud. The `queue_literal_then_empty_concat` fixture supplies the
differential `PASS` row and Lean receipt.

Differential coverage grows **351/345/0/6 → 352/346/0/6** with no
disagreements; grammar coverage remains **218/97/121**. The external corpus
snapshot remains unavailable, so the committed **5,401 clean / 16,597 partial**
counts and 67 include skips are unchanged.

## Source-pure string transformation assignments — 2026-10-28

Blocking assignments from `string.toupper()`, `string.tolower()`, and literal
bounded `string.substr(i, j)` now use the existing ASCII source-history path
when their receiver has only an earlier direct literal write. The opaque string
store is erased and later comparisons are folded from the transformed value;
dynamic, aliased, timed, nonblocking, and non-ASCII histories remain loud.

Differential coverage grows **352/346/0/6 → 354/348/0/6** with no
disagreements; grammar coverage remains **218/97/121**. The external corpus
snapshot remains unavailable, so the committed **5,401 clean / 16,597 partial**
counts and 67 include skips are unchanged.

## Power self-check differential rows — 2026-10-28

The integral power family is now registered in the executable differential
matrix with its unsigned, signed, and zero-to-negative self-check fixtures.
All three rows match the committed `PASS` declarations. The zero-to-negative
row continues to record the IEEE 1800-2023 §11.4.3 Table 11-4 and Icarus
all-x result as a documented divergence from the separate reference run; it
is not treated as a reference confirmation.

Differential coverage grows **348/342/0/6 → 351/345/0/6** with no
disagreements; grammar coverage remains **218/97/121**. The external corpus
snapshot remains unavailable, so the committed **5,401 clean / 16,597 partial**
counts and 67 include skips are unchanged.

## Fixed-array subarray self-copies — 2026-10-28

An exact blocking self-copy of one constant subarray of a fixed
multidimensional integral array now lowers to `Empty`, since every source
cell is already the matching destination cell. Nonblocking, overlapping,
dynamic, timed, and nonintegral forms remain loud. The
`fixed_array_subarray_self_copy` fixture supplies the differential `PASS`
row and Lean receipt.

Differential coverage grows **347/341/0/6 → 348/342/0/6** with no
disagreements; grammar coverage remains **218/97/121**. The external corpus
snapshot remains unavailable, so the committed **5,401 clean / 16,597 partial**
counts and 67 include skips are unchanged.

## Disjoint fixed-array subarray copies — 2026-10-28

A blocking copy between two constant subarrays of one fixed multidimensional
integral array is admitted when their flattened source and destination cell
sets are disjoint and have equal widths and lengths. The extractor lowers the
copy to cellwise writes, which preserves the complete source snapshot because
no destination write can change a later source read. Overlapping, dynamic,
timed, nonblocking, and nonintegral forms remain loud. The
`fixed_array_disjoint_subarray_copy` fixture supplies the differential
`PASS` row and Lean receipt.

Differential coverage grows **346/340/0/6 → 347/341/0/6** with no
disagreements; grammar coverage remains **218/97/121**. The external corpus
snapshot remains unavailable, so the committed **5,401 clean / 16,597 partial**
counts and 67 include skips are unchanged.

## Literal-return function operands in dynamic-array concatenations — 2026-10-28

An unpacked concatenation assigned to a scalar-integral dynamic array may
contain a zero-argument function whose complete body assigns one integral
literal through the implicit function name. The call is sampled as one scalar
cell after the extractor checks the declaration has no copy-out or reference
arguments. State-dependent, effectful, and otherwise unsupported function
operands remain loud. The `dynamic_array_concat_literal_function` fixture
supplies the differential `PASS` row and Lean receipt.

Differential coverage grows **345/339/0/6 → 346/340/0/6** with no
disagreements; grammar coverage remains **218/97/121**. The external corpus
snapshot remains unavailable, so the committed **5,401 clean / 16,597 partial**
counts and 67 include skips are unchanged.

## Invalid packed-dimension declarations — 2026-10-28

Declaration-only integral variables whose elaborated type is pyslang
`ErrorType` because of a malformed packed dimension now lower to no
declaration in the legacy self-check envelope. A rejected declaration has no
runtime object, so this preserves the compile-time error boundary without
inventing storage. The admission is limited to uninitialized integer type
syntax containing a packed dimension; ordinary 2-state declarations,
initialized malformed declarations, symbolic declarations, and references
remain loud. The `invalid_packed_dimension_decl` fixture supplies two malformed
declarations, a differential `PASS` row, and a direct Lean receipt.

Differential coverage grows **340/334/0/6 → 341/335/0/6** with no
disagreements; grammar coverage remains **218/97/121**. The external
22,065-file corpus is unavailable in this checkout, so its prior census
**5,401 clean / 16,597 partial** snapshot and 67 include skips are retained.

## Literal-initialized invalid packed dimensions — 2026-10-28

The same compile-time declaration admission now covers a direct integral
literal initializer. Pyslang exposes the initializer as `InvalidExpression`
because the type is already rejected, so the extractor checks the original
declaration spelling before erasing it. Calls and other effectful
initializers remain loud. The `invalid_packed_dimension_literal` fixture adds
the differential `PASS` row and Lean receipt.

Differential coverage grows **341/335/0/6 → 342/336/0/6** with no
disagreements; grammar coverage remains **218/97/121**. The external corpus
snapshot remains unavailable, so the committed **5,401 clean / 16,597
partial** counts and 67 include skips are unchanged.

## Source-pure fixed-array continuous copies — 2026-10-28

The legacy self-check extractor now admits a whole-array continuous assignment
when its one-dimensional fixed-unpacked variable source has a complete literal
declaration initializer and no later writes. The aggregate is expanded into
one time-zero write per destination cell, preserving ordinal correspondence
even when the source and destination ranges run in opposite directions. A
mutable source, net source, slice, dynamic array, timed or nonblocking form
remains loud because those cases need a live continuous-driver state. The
`static_fixed_array_continuous_copy` fixture supplies the differential `PASS`
row and Lean receipt.

Differential coverage grows **342/336/0/6 → 343/337/0/6** with no
disagreements; grammar coverage remains **218/97/121**. The external corpus
checkout is unavailable, so the committed **5,401 clean / 16,597 partial**
snapshot and 67 include skips are unchanged.

## Ignored string null-character assignments — 2026-10-28

The legacy self-check extractor now admits the IEEE §6.16 rule that assigning
integral zero to a selected string byte is ignored. The narrow lowering accepts
only a blocking literal-zero write with a constant index and emits `Empty`,
which is exact because the self-check state carries no string storage. Dynamic
indices, nonzero values, timed and nonblocking writes remain loud. The
`string_null_character` fixture supplies the differential `PASS` row and Lean
receipt.

Differential coverage grows **343/337/0/6 → 344/338/0/6** with no
disagreements; grammar coverage remains **218/97/121**. The external corpus
checkout is unavailable, so the committed **5,401 clean / 16,597 partial**
snapshot and 67 include skips are unchanged.

## Source-pure string replication writes — 2026-10-28

The legacy self-check extractor now resolves constant string replications and
concatenations when each named-string operand has only earlier unconditional
blocking ASCII literal history. The opaque string target is erased, while a
matching `%s` diagnostic receives the exact packed bytes. Uninitialized,
computed, control-dependent, timed, nonblocking, and non-ASCII histories stay
loud. The existing `replication/dynamic_string` fixture supplies the
`dynamic abab` differential `PASS` row and Lean receipt.

Differential coverage grows **344/338/0/6 → 345/339/0/6** with no
disagreements; grammar coverage remains **218/97/121**. The external corpus
checkout is unavailable, so the committed **5,401 clean / 16,597 partial**
snapshot and 67 include skips are unchanged.

The executable self-check and grammar baseline is generated in
[`docs/sv-coverage.md`](sv-coverage.md) by
`harness/sv_coverage_page.py`; its differential rows are pinned to the
self-check declarations and its grammar rows name one pyslang witness each.

## One-dimensional fixed-array `%p` diagnostics — 2026-10-27

The self-check surface now renders a direct one-dimensional fixed integral
array in `%p` diagnostics by reading the existing flattened cells in declared
index order. Nested, dynamic, effectful, and other-format aggregate arguments
remain loud; no aggregate store is introduced. The `array_named_display`
fixture supplies the differential witness and Lean receipt.

The chapter-only census moves **5,396 clean / 16,602 partial → 5,401 clean /
16,597 partial** over **22,065** files with 67 include skips;
`NamedValueExpression:2state` falls **1,473 → 1,462**. Differential coverage
grows **333/327/0/6 → 334/328/0/6** with no disagreements, while grammar
coverage remains **218/97/121**.

## Source-pure string equality and relational comparisons — 2026-10-27

String `==`, `!=`, `===`, `!==`, `<`, `<=`, `>`, and `>=` now fold to exact
one-bit literals for direct ASCII literals and named strings whose prior
history contains only unconditional blocking ASCII literal writes. Computed,
control-dependent, timed, nonblocking, dynamic, and non-ASCII histories stay
loud because the flat self-check state does not store general strings. The
`string_comparison_history` fixture supplies the differential witness and Lean
receipt.

The chapter-only census moves **5,384 clean / 16,614 partial → 5,396 clean /
16,602 partial** over **22,065** files with 67 include skips;
`NamedValueExpression:2state` falls **1,488 → 1,473** and the leading blockers
are unchanged. Differential coverage grows **332/326/0/6 → 333/327/0/6** with
no disagreements, while grammar coverage remains **218/97/121**.

## Explicit source-pure real-to-integral casts — 2026-10-27

Explicit casts from a finite `real` or `shortreal` source to an integral
target now fold to the nearest integer, with ties away from zero, before the
existing target-width conversion. A direct literal or a source-ordered direct
blocking literal history is sufficient; computed, control-dependent, timed,
non-finite, and dynamic real sources remain loud because the flat self-check
state does not model general floating storage. The `real_integral_cast`
fixture supplies the differential witness and Lean receipt.

The chapter-only census moves **5,359 clean / 16,639 partial → 5,384 clean /
16,614 partial** over **22,065** files with 67 include skips;
`ConversionExpression:Explicit` falls **34 → 9** and the leading blockers are
unchanged. Differential coverage grows **331/325/0/6 → 332/326/0/6** with no
disagreements, while grammar coverage remains **218/97/121**.

## Named literal-history `$timeformat` — 2026-10-27

`$timeformat` now accepts source-pure named integral unit, precision, and
width arguments when source order proves direct blocking literal histories
and the source has no `%t` consumer. The self-check state carries no time
format register, so the validated call remains inert; `%t` consumers,
computed, control-dependent, timed, nonblocking, and dynamic forms remain
loud. The `timeformat_named_history` fixture supplies the differential
witness; coverage grows **328/322/0/6 → 329/323/0/6**, grammar remains
**218/97/121**, and the chapter-only census remains **5,331 clean / 16,667
partial** with 67 include skips.

## Named literal-history `$assertcontrol` — 2026-10-27

`$assertcontrol` now accepts integral arguments established by direct
blocking literals in the time-zero initial history. Assertion-control state is
not represented in the self-check envelope, so the call remains an inert
`Empty` after source-order validation. Computed, control-dependent, timed,
nonblocking, and dynamic arguments remain loud. The
`assertcontrol_named_history` fixture supplies the differential witness;
coverage grows **327/321/0/6 → 328/322/0/6**, grammar remains **218/97/121**,
and the chapter-only census remains **5,331 clean / 16,667 partial** with 67
include skips.

## Discarded bit queries over named literal history — 2026-10-27

Statement-position `$countbits`, `$countones`, `$onehot`, `$onehot0`, and
`$isunknown` calls now accept named integral operands when source order proves
that each declaration and earlier write is a direct blocking literal in the
time-zero initial history. Their scalar result is discarded, so no query
state is added to the self-check envelope. Computed, control-dependent,
timed, nonblocking, and dynamic histories remain loud. The
`bit_query_named_history` fixture supplies the differential witness; coverage
grows **326/320/0/6 → 327/321/0/6**, while grammar coverage remains
**218/97/121** and the chapter-only census remains **5,331 clean / 16,667
partial** with 67 include skips.

## Time-zero `$realtime` conversions — 2026-10-27

The expression tier now folds `$rtoi($realtime)`, `$realtobits($realtime)`,
and `$shortrealtobits($realtime)` to exact zero literals only inside an
untimed `initial` process. Continuous assignments, `always` processes,
delayed/event/waiting initials, direct real storage, and other elapsed-time
uses remain loud. The `realtime_conversion_calls` fixture supplies the
differential witness and Lean receipt.

The chapter-only census remains **5,327 clean / 16,670 partial** (67 include
skips); `CallExpression` falls **2,655 → 2,648**. Differential coverage grows
**325/319/0/6 → 326/320/0/6** and grammar remains **218/97/121**.

## Source-pure named-integral `$itor` — 2026-10-27

The expression tier now folds `$itor` over a named integral whose declaration
or earlier writes are direct literals, feeding only the exact `$rtoi`,
`$realtobits`, and `$shortrealtobits` paths. Computed, control-dependent,
timed, nonblocking, dynamic, and standalone real-storage forms remain loud.
The `itor_named_integral_history` fixture supplies the differential witness
and Lean receipt.

The chapter-only census remains **5,327 clean / 16,670 partial** (67 include
skips), while differential coverage grows **324/318/0/6 → 325/319/0/6** and
grammar remains **218/97/121**.

## Timed literal `$q_exam` statistics — 2026-10-27

The surface now admits a single straight-line literal queue history with empty
literal delays. Codes 2, 4, 5, and 6 are calculated from the source-ordered
tick timeline and lower to the existing scalar output assignments. One initial
process, literal queue IDs or one direct literal ID write, successful scalar
adds, nonempty scalar removes, and direct output lvalues are required; dynamic
delays, overflow, branches, additional processes, and computed or aliased
histories remain loud. The `q_exam_timed_statistics` receipt advances the
existing timed scheduler at 4 and 6 ticks and checks its PASS transcript; the
time-zero differential runner intentionally keeps timed calls as refusals.

The four timed corpus witnesses reduce `ExpressionStatement:CallExpression`
from **2,722 to 2,718**. The current 22,065-file chapter walk is **5,331 clean /
16,667 partial** with 67 include skips; one new upstream partial file accounts
for the denominator change from the prior 22,064 snapshot. Differential coverage
stays **326/320/0/6**, and grammar coverage stays **218/97/121**.

## Source-pure named-real `$rtoi` — 2026-10-27

The expression tier now folds `$rtoi` over a finite named real or short-real
when source order proves only direct literal assignments have occurred. The
decimal conversion truncates toward zero into the existing signed 32-bit
literal representation; computed, control-dependent, timed, nonblocking,
dynamic, and out-of-range histories remain loud. The
`rtoi_named_real_history` fixture supplies the differential witness and Lean
receipt.

The chapter-only census remains **5,327 clean / 16,670 partial** (67 include
skips), while differential coverage grows **323/317/0/6 → 324/318/0/6** and
grammar remains **218/97/121**.

## Mailbox `try_peek()` type mismatch — 2026-10-27

The surface now admits an untyped mailbox containing one scalar integral
literal when `try_peek()` receives a destination of a non-equivalent type.
IEEE 1800-2023 §15.4.8 specifies a negative return and no destination write or
FIFO consumption, so the flat self-check lowering carries no mailbox or
scheduler state. Aliases, dynamic or multiple histories, equivalent types, and
other mailbox operations remain loud. The
`mailbox_try_peek_type_mismatch` fixture supplies the differential witness and
Lean receipt.

The 22,064-path census moves **5,326 → 5,327 clean / 16,671 → 16,670 partial**
(67 include skips); `CallExpression` falls **2,656 → 2,655** while
`ExpressionStatement:CallExpression` remains **2,722**. Differential coverage
grows **322/316/0/6 → 323/317/0/6** with no disagreements; grammar remains
**218/97/121**.

## Source-pure variable bounds for `$dist_uniform` — 2026-10-27

Direct blocking scalar assignments from `$dist_uniform` now accept signed
32-bit bound variables when each has exactly one earlier blocking assignment
from an integral literal in the same initial process. The existing explicit
seed recurrence and scalar cell write remain the semantics; declaration
initializers, computed or reassigned bounds, nonblocking or timed writes,
non-32-bit bounds, and value-position random calls remain loud. The
`dist_uniform_variable_bounds` fixture mirrors the §18.13.3 bounded-loop shape
and supplies the differential row and Lean receipt.

The committed chapter-only census remains **5,326 clean / 16,671 partial**
(67 include skips), because the upstream witness is a root-level file outside
that walk. Differential coverage grows **321/315/0/6 → 322/316/0/6** with no
disagreements; grammar remains **218/97/121**.

## Literal queue-to-fixed-array size mismatch — 2026-10-27

The surface now recognizes a direct scalar-literal queue copied to a
differently sized fixed unpacked integral array. IEEE 1800-2023 §7.6 makes the
copy a run-time error with no partial update; the flat self-check lowering
therefore emits the existing immediate `$finish` after any earlier output.
Equal-size queue copies continue through the cellwise lowering, while dynamic,
aliased, mutated, aggregate, timed, and nonblocking histories remain loud. The
`queue_fixed_size_mismatch` fixture supplies the `BEFORE` transcript and Lean
receipt.

The current 22,064-path census moves **5,325 → 5,326 clean / 16,672 → 16,671
partial** (67 include skips); `AssignmentExpression:target` falls **2,844 →
2,842**. Differential coverage grows **320/314/0/6 → 321/315/0/6** with no
disagreements; grammar remains **218/97/121**.

## Fixed-size `$bits` operands — 2026-10-27

`$bits(expr)` now reads the elaborated width of any fixed-size bitstream
operand without evaluating or converting `expr`, as required by IEEE
1800-2023 §20.6.2. Increments, assignments, function calls, and selected
reads therefore remain metadata-only when their result type is fixed. The
`bits_fixed_expr` fixture proves that a post-increment is not observed by the
self-check state. Initialized dynamic strings, queues, associative arrays,
and other runtime-sized or non-bitstream operands remain loud; the existing
empty dynamic-array/string metadata cases are unchanged.

The 22,059-path census remains **5,304 clean / 16,688 partial** (67 include
skips), while `CallExpression` falls **2,729 → 2,672**. Differential coverage
grows **318/312/0/6 → 319/313/0/6** with no disagreements; grammar remains
**218/97/121**.

## Literal mailbox `peek()` and `try_peek()` — 2026-10-27

Source-ordered mailbox histories made from scalar literals now admit the FIFO
copy operations `peek()` and `try_peek()`. Both preserve the queue, while
`try_peek()` also copies the success flag and output value; typed mailboxes
require the same fixed width as the destination. Empty blocking peeks,
dynamic messages, aliases, branches, and width mismatches remain loud because
the flat self-check state still carries no mailbox object. The
`mailbox_literal_peek` fixture supplies the differential witness and Lean
receipt.

The 22,059-path census snapshot remains **5,304 clean / 16,688 partial** (67
include skips). Differential coverage grows **319/313/0/6 → 320/314/0/6**
with no disagreements; grammar remains **218/97/121**.

## Literal queue initializer `.size()` — 2026-10-27

A 2-state queue initialized only by scalar literals now answers `.size()`
with its exact compile-time element count. The declaration and query carry no
queue object into the flat self-check state; pushes, pops, deletes, aliases,
content reads, dynamic initializers, and value-position aggregate operations
remain loud. `queue_literal_size` supplies the differential witness and Lean
receipt.

The 22,059-path census remains **5,301 clean / 16,691 partial** (67 include
skips); `VariableSymbol:2state` falls **2,223 → 2,118**, while
`ExpressionStatement:CallExpression` remains **2,739**. Differential coverage
grows **315/309/0/6 → 316/310/0/6** with no disagreements; grammar remains
**218/97/121**.

## Literal queue empty reassignment `.size()` — 2026-10-27

A direct empty queue assignment after a scalar-literal initializer now updates
the source-ordered size query to exact zero. Further empty assignments and
size reads remain pure; nonempty mutations, aliases, content reads, dynamic or
effectful assignments, and value-position aggregate operations remain loud.
`queue_literal_size_after_empty_write` supplies the differential witness and
Lean receipt.

The 22,059-path census moves **5,301 → 5,303 clean / 16,691 → 16,689
partial** (67 include skips); `CallExpression` falls **2,731 → 2,729** while
`ExpressionStatement:CallExpression` remains **2,739**. Differential coverage
grows **316/310/0/6 → 317/311/0/6** with no disagreements; grammar remains
**218/97/121**.

## Literal `unique case` subset — 2026-10-27

The surface now admits `unique case` when each pattern is a direct integral
literal, patterns are duplicate-free, and either a default arm handles every
other value or the patterns cover all values of a subject no wider than eight
bits on a two-state subject. This removes the diagnostic side effect for the
admitted forms while keeping dynamic, duplicate, incomplete, wildcard,
four-state complete-without-default, `unique0`, and `priority` cases loud.
The `unique_case_complete` fixture supplies a complete two-bit case, with
extractor regressions for the default, duplicate, and incomplete boundaries.

The 22,059-path corpus moves **5,294 → 5,298 clean / 16,698 → 16,694
partial** (67 include skips); `CaseStatement:Unique` falls **45 → 41** while
`ExpressionStatement:CallExpression` remains **2,739**. Differential coverage
grows **311 rows / 306 matches / 0 disagreements / 5 refusals → 312 / 307 /
0 / 5** with no disagreements; grammar remains **218/96/122**.

## Literal ASCII string `$sformatf` — 2026-10-27

The literal `$sformatf` expression slice now accepts an ASCII string literal
as the sole `%s` or `%S` operand. Its packed bytes use the existing string
renderer and remain pure; dynamic string variables, non-ASCII text, aggregates,
and other string storage stay loud. The `sformatf_string_literal` fixture
supplies the extractor regression, Lean receipt, and differential row.

The 22,059-path corpus remains **5,287 clean / 16,705 partial** (67 include
skips); `ExpressionStatement:CallExpression` remains **2,746** and
`CallExpression` remains **2,739**. Differential coverage grows
**306/301/0/5 → 307/302/0/5** with no disagreements; grammar remains
**218/96/122**.

## Source-pure named ASCII string `$sformatf` — 2026-10-27

The literal `$sformatf` expression slice now accepts a named `string` when its
initializer and every source assignment are blocking ASCII literals. The
latest proven bytes are lowered to the existing packed `%s`/`%S` renderer, so
the flat self-check state does not acquire dynamic string storage. Unassigned,
dynamic, nonblocking, timed, non-ASCII, aggregate, and other value histories
remain loud. The `sformatf_string_history` fixture supplies the extractor
regression, Lean receipt, and differential row.

The 22,059-path corpus remains **5,287 clean / 16,705 partial** (67 include
skips); `ExpressionStatement:CallExpression` remains **2,746** and
`CallExpression` remains **2,739**; the residual
`CallExpression:$sformatf:format` wall falls **6 → 4**. Differential coverage grows
**307/302/0/5 → 308/303/0/5** with no disagreements; grammar remains
**218/96/122**.

## Literal integral zero-width `$sformatf` — 2026-10-27

Literal integral `$sformatf` expressions now accept `%0b/%0h/%0o/%0d` and
their uppercase aliases. The existing renderer strips the leading binary and
hexadecimal zeroes, keeps the packed octal width rule, and emits minimal
decimal text. Dynamic formats, other field controls, and nonintegral operands
remain loud. The `sformatf_zero_width` fixture supplies the extractor
regression, Lean receipt, and differential row.

The 22,059-path corpus remains **5,287 clean / 16,705 partial** (67 include
skips); `ExpressionStatement:CallExpression` remains **2,746** and
`CallExpression` remains **2,739**. Differential coverage grows
**305/300/0/5 → 306/301/0/5** with no disagreements; grammar remains
**218/96/122**.

## Literal integral character `$sformatf` — 2026-10-27

Expression-position `$sformatf` now admits `%c` and `%C` for one literal
integral operand. The low byte renders as an ASCII packed character through
the existing formatter, including when the result is passed to `$display`.
Unknown bits, dynamic formats, string or aggregate operands, and other
conversion forms remain loud. The `sformatf_char` fixture supplies the
extractor regression, Lean receipt, and differential row.

The 22,059-path corpus remains **5,287 clean / 16,705 partial** (67 include
skips); `ExpressionStatement:CallExpression` remains **2,746** and
`CallExpression` remains **2,739**. Differential coverage grows
**304/299/0/5 → 305/300/0/5** with no disagreements; grammar remains
**218/96/122**.

## Discarded literal `$sformatf` statements — 2026-10-27

Statement-position `$sformatf` now reuses the admitted expression converter
for one literal format and one pure integral operand, then erases the packed
result. `%b/%h/%o/%d` and their uppercase aliases are covered; dynamic formats,
extra arguments, unsupported conversions, real or aggregate operands, and
other string state remain loud. The `sformatf_statement` fixture supplies the
Lean receipt, extractor regression, and differential row.

The 22,059-path corpus remains **5,287 clean / 16,705 partial** (67 include
skips); `ExpressionStatement:CallExpression` remains **2,746** and
`AssignmentExpression:target` remains **2,852**. Differential coverage grows
**303/298/0/5 → 304/299/0/5** with no disagreements; grammar remains
**218/96/122**.

## Literal zero-time `$q_exam` histories — 2026-10-27

The self-check surface now replays a source-ordered literal FIFO/LIFO queue
through `$q_exam` and `$q_remove` without adding a runtime queue object. Code 1
returns the exact current length after successful static removals, code 3
continues to return the maximum length, and codes 2, 4, 5, and 6 return zero
for a history with no delay or event control. The queue history requires
literal IDs and payloads (or the existing single prior literal assignments),
nonempty removals, and direct output lvalues. Timed, computed, empty, and
other queue forms remain loud. `q_exam_static_history` supplies the
extractor regression, Lean receipt, and differential row.

The 22,059-path corpus moves **5,286 → 5,287 clean** and **16,706 → 16,705
partial** (67 include skips); `ExpressionStatement:CallExpression` falls
**2,747 → 2,746** while `AssignmentExpression:target` remains **2,852**.
Differential coverage grows **302/297/0/5 → 303/298/0/5** with no
disagreements; grammar remains **218/96/122**.

## Literal integral `$sformatf` expressions — 2026-10-27

Expression-position `$sformatf` calls now admit one literal format and one
pure integral operand for `%b/%h/%o/%d`, with `%B/%H/%O/%D` sharing the same
renderer. The returned text is an ASCII packed value in the self-check state,
so existing equality and four-state rendering rules remain the semantic core.
Dynamic formats, extra arguments, unsupported conversions, real or aggregate
operands, and dynamic string storage remain loud. The `sformatf_uppercase`
fixture and extractor regressions pin both the accepted aliases and the
refusal boundaries.

The 22,059-path corpus moves **5,273 → 5,274 clean** and **16,719 → 16,718
partial** (67 include skips); `ExpressionStatement:CallExpression` remains
**2,759** and `CallExpression` falls **2,750 → 2,739**. Differential coverage
grows **300/295/0/5 → 301/296/0/5** with no disagreements; grammar remains
**218/96/122**.

## Literal FIFO/LIFO queue payload removal — 2026-10-27

The self-check surface now admits a source-ordered queue history containing
one literal FIFO or LIFO `$q_initialize`, literal `$q_add` entries, and
nonempty `$q_remove` calls. Each removal is lowered to ordinary scalar writes
for the returned job, inform, and status values, preserving queue order and
capacity without introducing a runtime queue object. Computed payloads,
empty removals, timing, branches, other queue tasks, and value-position forms
remain loud. The `q_remove_payload` fixture and extractor regressions pin the
FIFO boundary.

The 22,059-path corpus moves **5,274 → 5,286 clean** and **16,718 → 16,706
partial** (67 include skips); `ExpressionStatement:CallExpression` falls
**2,759 → 2,747** while `AssignmentExpression:target` remains **2,852**.
Differential coverage grows **301/296/0/5 → 302/297/0/5** with no
disagreements; grammar remains **218/96/122**.

## Named literal queue history for `$q_exam` — 2026-10-27

Queue status calls now resolve a direct named operand from exactly one prior
blocking literal assignment in the same source instance. This admits the
sv-tests-2 `$q_exam` statistic-code shape: `q_id`, `job_id`, and `inform_id`
are sampled before a literal FIFO/LIFO initialization, `$q_add` history is
counted source-order, and statistic codes 1 and 3 write the current or maximum
length followed by status 0. Unassigned, computed, timed, nonblocking, or
reassigned operands, other statistic codes, removals, and value-position forms
remain loud; queue payload storage is still not represented.

The `q_exam_stat_codes` fixture supplies the named-history transcript, extractor
regressions, Lean receipt, and differential row. The 22,059-path census moves
**5,272 → 5,273 clean** and **16,720 → 16,719 partial** (67 include skips);
`ExpressionStatement:CallExpression` falls **2,760 → 2,759** while
`CallExpression` remains **2,750**. Differential coverage grows
**299/294/0/5 → 300/295/0/5** with no disagreements; grammar remains
**218/96/122**.

## Bounded dynamic `$dist_uniform` fixed-array writes — 2026-10-27

The self-check surface now admits an assignment whose RHS is
`$dist_uniform(seed, 0, 1000)` and whose destination is a one-dimensional
finite fixed-unpacked integral array selected by a pure integral index. The
32-bit seed is updated and the selected flattened cell is written in the same
branch; repeated seeds therefore produce the same sequence while the update
remains explicit state rather than an invented random oracle. The admitted
slice requires a direct 32-bit variable seed, literal bounds `0` and `1000`,
and a 32-bit array element. Other bounds, seed expressions, aggregate or
dynamic storage, effectful selectors, and value-position random calls remain
loud.

`dist_uniform_array_target` supplies the repeatability fixture, extractor
regression, Lean receipt, and differential row. The 22,059-path census moves
**5,253 → 5,254 clean** and **16,739 → 16,738 partial** (67 include skips);
`AssignmentExpression:target` falls **2,853 → 2,852**. Differential coverage
grows **294/289/0/5 → 295/290/0/5** with no disagreements; grammar coverage
remains **218/95/123**.

## Seeded bounded `$dist_uniform` scalar assignments — 2026-10-27

IEEE 1800-2023 §20.14.2 permits a seeded distribution function to update its
inout seed and return an integer in the inclusive bounds. The self-check slice
now admits direct blocking assignments from `$dist_uniform(seed, 0, 1000)` to
32-bit integral scalar cells, using the explicit deterministic recurrence and
retaining the seed update. Computed seeds, other bounds, nonblocking or timed
forms, non-32-bit targets, and value-position calls remain loud. The
`dist_uniform_scalar` fixture and four chapter-20 witnesses supply the
repeatability/range evidence.

The 22,059-path census moves **5,254 → 5,258 clean** and **16,738 → 16,734
partial** (67 include skips); `CallExpression` falls **2,768 → 2,764** while
`AssignmentExpression:target` remains **2,852**. Differential coverage gains
one matching row; grammar coverage is regenerated with the current witness
set.

## Nonnegative literal `$dist_uniform` scalar bounds — 2026-10-27

IEEE 1800-2023 §20.14.2's inclusive start/end contract now covers any
nonnegative literal pair within the signed 32-bit range for direct blocking
assignments. The explicit recurrence retains the inout seed update; negative
or computed bounds, nonblocking or timed forms, non-32-bit targets, and
value-position calls remain loud. `dist_uniform_literal_bounds` supplies the
fixture and ten additional chapter-20 witnesses become clean.

The 22,059-path census moves **5,258 → 5,268 clean** and **16,734 → 16,724
partial** (67 include skips); `CallExpression` falls **2,764 → 2,754** while
`AssignmentExpression:target` remains **2,852**. Differential coverage grows
**296/291/0/5 → 297/292/0/5**; grammar moves **218/95/123 → 218/96/122**.

## Signed literal `$dist_uniform` scalar bounds — 2026-10-27

The direct scalar assignment rung now accepts signed literal start/end pairs
within the 32-bit integer range, including wholly negative and zero-crossing
ranges. The explicit recurrence updates the inout seed and encodes the result
with two's-complement bits before the existing signed comparisons observe it.
Computed bounds, reversed or out-of-range pairs, nonblocking or timed forms,
non-32-bit targets, and value-position calls remain loud. The
`dist_uniform_signed_bounds` fixture covers both negative and crossing ranges;
the two corresponding chapter-20 witnesses become clean.

The 22,059-path census moves **5,268 → 5,270 clean** and **16,724 → 16,722
partial** (67 include skips); `CallExpression` falls **2,754 → 2,752** while
`AssignmentExpression:target` remains **2,852**. Differential coverage grows
**297/292/0/5 → 298/293/0/5**; grammar remains **218/96/122**.

## `$q_full` value calls after prior status checks — 2026-10-27

Value-position `$q_full` now retains the existing literal queue-history model
when the separate status output has only been read before the first query.
Initialization and literal-add statuses remain represented scalar writes, while
the query value is derived from the source-ordered capacity counter. Reads of
an unmodeled `$q_full` status after the first query, symbolic IDs, payload
observations, removals, and other queue operations remain loud. The
`q_full_value_history` fixture supplies the two query results and the
source-order status check.

The 22,059-path census moves **5,270 → 5,272 clean** and **16,722 → 16,720
partial** (67 include skips); `CallExpression` falls **2,752 → 2,750** while
`ExpressionStatement:CallExpression` and `AssignmentExpression:target` remain
**2,760** and **2,852**. Differential coverage grows **298/293/0/5 →
299/294/0/5**; grammar remains **218/96/122**.

## Queue-removal status — 2026-10-27

IEEE 1800-2023 §20.15.6 gives scalar statuses for queue removal without
requiring queue payload storage in the self-check state. An uninitialized
literal queue ID now lowers `$q_remove` to status 2. A valid literal FIFO/LIFO
initialization followed by one removal from the still-empty queue lowers the
initialization to 0 and the removal to status 3. Named IDs require one direct
literal assignment, and job/inform outputs must remain unread. Populated,
payload-observing, computed, and additional queue operations remain loud.
`q_remove_status_2` and `q_remove_status_3` supply the PASS transcripts,
extractor regressions, and capped Lean receipts.

The 22,059-path census moves **5,241 → 5,243 clean** and **16,751 → 16,749
partial** (67 include skips); `ExpressionStatement:CallExpression` falls
**2,774 → 2,772**, while `AssignmentExpression:target` remains **2,853**.
Differential coverage grows **284/279/0/5 → 286/281/0/5**; grammar coverage
is regenerated with the current witness count.

## Queue-add status — 2026-10-27

IEEE 1800-2023 §20.15.2 defines scalar status results for `$q_add`. A
source-ordered literal `$q_initialize` followed by literal FIFO/LIFO adds now
retains only the status output: successful additions report 0, and the first
addition after the positive capacity reports 1. Queue IDs, job and inform
arguments must be integral literals, and no other queue operation is admitted;
symbolic IDs, payload expressions, populated observations, and value-position
forms remain loud. `q_add_status_0` and `q_add_status_1_when_full` supply the
PASS transcripts, extractor regressions, and capped Lean receipts.

The 22,059-path census moves **5,243 → 5,245 clean** and **16,749 → 16,747
partial** (67 include skips); `ExpressionStatement:CallExpression` falls
**2,772 → 2,770**, while `AssignmentExpression:target` remains **2,853**.
Differential coverage grows **286/281/0/5 → 288/283/0/5**; grammar coverage
remains **218/95/123**.

## Queue-full status — 2026-10-27

IEEE 1800-2023 §20.15.4 defines the scalar result of `$q_full`. A literal
queue initialization with only literal adds and full queries now lowers each
query to 0 while the count is below capacity and to 1 once capacity is
reached. Both direct status-output statements and value-position queries with
an unread status output are admitted; symbolic IDs, observed status side
effects, other queue operations, and payload expressions remain loud.
`q_full_status_0` and `q_full_status_1_when_full` supply the PASS transcripts,
extractor regressions, and capped Lean receipts.

The 22,059-path census moves **5,245 → 5,249 clean** and **16,747 → 16,743
partial** (67 include skips); `ExpressionStatement:CallExpression` falls
**2,770 → 2,764**, while `AssignmentExpression:target` remains **2,853**.
Differential coverage grows **288/283/0/5 → 290/285/0/5**; grammar coverage
remains **218/95/123**.

## Queue-exam length statistics — 2026-10-27

IEEE 1800-2023 §20.15.5 Table 20-10 defines `$q_exam` statistic codes 1 and
3 as the current and maximum queue lengths. A source-ordered literal
`$q_initialize` followed only by literal `$q_add` history and these two
statistics now writes the statistic value and then status 0. The flat model
clamps successful additions at the literal capacity; removal, timing,
symbolic IDs, other statistic codes, and value-position forms remain loud.
`q_exam_length`, `q_exam_current_length`, `q_exam_max_queue_length`, and
`q_exam_stat_code_3_max_length_v3` supply the PASS transcripts, extractor
regressions, and capped Lean receipts.

The 22,059-path census moves **5,249 → 5,253 clean** and **16,743 → 16,739
partial** (67 include skips); `ExpressionStatement:CallExpression` falls
**2,764 → 2,760**, while `AssignmentExpression:target` remains **2,853**.
Differential coverage grows **290/285/0/5 → 294/289/0/5**; grammar coverage
remains **218/95/123**.

## Duplicate queue-ID status — 2026-10-27

IEEE 1800-2023 §20.15.6 gives a duplicate queue ID status without exposing
the queue contents. The legacy self-check surface now lowers two source-pure
`$q_initialize` calls with the same literal FIFO/LIFO type and positive
capacity to scalar writes: the first reports 0 and the duplicate reports 6.
A named ID must have one direct literal assignment before the calls. Other
queue operations, computed or reassigned IDs, invalid first creations, and
value-position forms remain loud. `q_initialize_duplicate_status` supplies the
PASS transcript, extractor regressions, and a capped Lean receipt.

The 22,059-path census moves **5,240 → 5,241 clean** and **16,752 → 16,751
partial** (67 include skips); `ExpressionStatement:CallExpression` falls
**2,775 → 2,774**, while `AssignmentExpression:target` remains **2,853**.
Differential coverage grows **283/278/0/5 → 284/279/0/5**; grammar coverage
is regenerated with the current witness count.

## Discarded invalid literal `$fopen` modes — 2026-10-26

An invalid literal mode in a discarded `$fopen(path, mode)` statement now
lowers through the existing deterministic zero-result converter. Validation
still precedes erasure, so valid modes, dynamic file arguments, and
value-position calls remain loud at the file-state boundary. The
`fopen_invalid_mode_statement` fixture supplies the self-check differential
row and Lean receipt; Icarus agrees with its `PASS` transcript (and reports
its standard invalid-mode warning).

The 22,059-path census remains **5,240 clean / 16,752 partial** (67 include
skips), with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**268/263/0/5 → 269/264/0/5** and grammar coverage remains **217/92/125**.

## Discarded empty associative-array count queries — 2026-10-26

Discarded `num()` and `size()` calls on a proven untouched 2-state associative
array now erase their exact zero result through the existing empty-array
converter. Populated, aliased, initialized, dynamic, and value-position
queries remain loud because their count depends on runtime state. The
`assoc_empty_query_statement` fixture supplies the self-check differential row
and Lean receipt; the pinned oracle agrees with its `PASS` transcript.

The 22,059-path census remains **5,240 clean / 16,752 partial** (67 include
skips), with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**269/264/0/5 → 270/265/0/5** and grammar coverage remains **217/92/125**.

## Discarded empty associative-array endpoint queries — 2026-10-26

Discarded `first(index)` and `last(index)` calls on a proven untouched 2-state
associative array now erase their exact zero result through the existing empty
endpoint converter. The direct named index argument remains checked; populated,
aliased, initialized, dynamic, and value-position queries stay loud. The
`assoc_empty_endpoint_statement` fixture supplies the self-check differential
row and Lean receipt; the pinned oracle agrees with its `PASS` transcript.

The 22,059-path census remains **5,240 clean / 16,752 partial** (67 include
skips), with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**270/265/0/5 → 271/266/0/5** and grammar coverage remains **217/92/125**.

## Discarded zero-size queries — 2026-10-26

Discarded `size()` calls on untouched queues or dynamic arrays, and `len()` on
an untouched empty string, now erase their exact scalar zero through the
existing zero-size converter. Mutation, aliases, initialized nonempty values,
and value-position observations remain loud. The `zero_size_statement` fixture
supplies the self-check differential row and Lean receipt; the pinned oracle
agrees with its `PASS` transcript.

The 22,059-path census remains **5,240 clean / 16,752 partial** (67 include
skips), with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**271/266/0/5 → 272/267/0/5** and grammar coverage remains **217/92/125**.

## Discarded literal-string queries — 2026-10-26

Discarded `len`, `getc`, `atoi`, radix, `compare`, and `icompare` calls on
unchanged ASCII literal strings now erase their scalar result through the
existing source-history converters. Non-ASCII strings, dynamic or mutated
receivers, aliases, unsupported conversions, and value-position observations
remain loud. The `string_query_statement` fixture supplies the self-check
differential row and Lean receipt; the pinned oracle agrees with its `PASS`
transcript.

The 22,059-path census remains **5,240 clean / 16,752 partial** (67 include
skips), with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**272/267/0/5 → 273/268/0/5** and grammar coverage remains **217/92/125**.

## Discarded literal-string `atoreal()` conversions — 2026-10-26

A discarded `atoreal()` call on an unchanged ASCII literal string now erases
its opaque real result through the existing source-history converter. Dynamic
strings, nonliteral writes, and value-position real conversions remain loud.
The `string_atoreal_statement` fixture supplies the self-check differential
row and Lean receipt; the pinned oracle agrees with its `PASS` transcript.

The 22,059-path census remains **5,240 clean / 16,752 partial** (67 include
skips), with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**273/268/0/5 → 274/269/0/5** and grammar coverage remains **217/92/125**.

## Discarded pre-trigger `event.triggered()` queries — 2026-10-26

Discarded `event.triggered()` calls on untouched events now erase their exact
pre-trigger false result through the existing event-history converter.
Triggered, dynamic, and value-position queries remain loud. The
`event_triggered_statement` fixture supplies the self-check differential row
and Lean receipt; the pinned oracle agrees with its `PASS` transcript.

The 22,059-path census remains **5,240 clean / 16,752 partial** (67 include
skips), with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**274/269/0/5 → 275/270/0/5** and grammar coverage remains **217/92/125**.

## Discarded enum `.name()` queries — 2026-10-26

Discarded `enum.name()` calls now reuse the existing enum method converter and
erase the unobserved string result after receiver and declaration-order checks.
Numeric enum methods, effectful receivers, malformed calls, and value-position
queries remain loud. The `enum_name_statement` fixture supplies the self-check
differential row and Lean receipt; the pinned oracle agrees with its `PASS`
transcript.

The 22,059-path census remains **5,240 clean / 16,752 partial** (67 include
skips), with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**275/270/0/5 → 276/271/0/5** and grammar coverage remains **217/92/125**.

## Discarded numeric enum queries — 2026-10-26

Discarded numeric enum methods (`first`, `last`, `num`, `next`, and `prev`)
now reuse the existing pure enum converter and erase their unobserved scalar
results after receiver and step checks. Dynamic or effectful receivers,
malformed methods, and value-position calls remain loud. The
`enum_numeric_statement` fixture supplies the self-check differential row and
Lean receipt; the pinned oracle agrees with its `PASS` transcript.

The 22,059-path census remains **5,240 clean / 16,752 partial** (67 include
skips), with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**276/271/0/5 → 277/272/0/5** and grammar coverage remains **217/92/125**.

## Discarded literal-string transformations — 2026-10-26

Discarded `toupper()`, `tolower()`, and literal-bound `substr()` calls now
erase their fresh string result after the existing ASCII source-history check.
Dynamic, aliased, mutated, non-ASCII, symbolic, and value-position forms remain
loud. The `string_transform_statements` fixture supplies the self-check
differential row and Lean receipt; the pinned oracle agrees with its `PASS`
transcript.

The 22,059-path census remains **5,240 clean / 16,752 partial** (67 include
skips), with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**278/273/0/5 → 279/274/0/5** and grammar coverage remains **217/92/125**.

## Discarded fixed-array locator queries — 2026-10-26

Discarded `min()`, `max()`, `unique()`, and `unique_index()` calls now erase
their unobserved queue result for named fixed-size arrays with integral leaves
when no `with` clause is present. Dynamic, queue, associative, aggregate,
`with`, symbolic, and value-position forms remain loud. The
`array_query_statements` fixture supplies the self-check differential row and
Lean receipt; the pinned oracle agrees with its `PASS` transcript.

The 22,059-path census remains **5,240 clean / 16,752 partial** (67 include
skips), with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**279/274/0/5 → 280/275/0/5** and grammar coverage grows **217/92/125 →
218/93/125**.

## Discarded fixed-array locator `with` queries — 2026-10-26

The same discarded `min()`, `max()`, `unique()`, and `unique_index()` queries
now accept a source-pure integral `with` expression after the existing iterator
purity check. Effectful `with` clauses remain loud. The
`array_query_with_statements` fixture supplies the self-check differential row
and Lean receipt; the pinned oracle agrees with its `PASS` transcript.

The 22,059-path census remains **5,240 clean / 16,752 partial** (67 include
skips), with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**280/275/0/5 → 281/276/0/5** and grammar coverage grows **218/93/125 →
218/95/123**.

## Discarded empty aggregate deletes — 2026-10-27

`delete()` on a source-pure empty queue or uninitialized dynamic array now
erases as an inert statement. Initialized, populated, aliased, effectful, and
symbolic aggregate forms remain loud. The `empty_aggregate_delete_statements`
fixture supplies the differential row and Lean receipt.

The 22,059-path census remains **5,240 clean / 16,752 partial** (67 include
skips), with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**. Differential coverage grows
**281/276/0/5 → 282/277/0/5** with no disagreements; grammar coverage remains
**218/95/123**.

## Discarded empty associative-array deletes — 2026-10-27

An untouched 2-state associative array now erases discarded `delete()` calls
for the whole array or a source-pure integral/string key. Initialized,
four-state, effectful-key, aliased, and symbolic forms remain loud. The
`empty_associative_delete_statements` fixture supplies the differential row and
Lean receipt.

The 22,059-path census remains **5,240 clean / 16,752 partial** (67 include
skips), with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**. Differential coverage grows
**282/277/0/5 → 283/278/0/5** with no disagreements; grammar coverage remains
**218/95/123**.

## Discarded fixed-array reductions — 2026-10-26

Discarded fixed-array reductions (`sum`, `product`, `and`, `or`, and `xor`)
now reuse the balanced value lowering after storage-shape, width, iterator, and
purity checks. The existing empty-dynamic-array identity also permits discarded
`sum` and `product`; other dynamic storage, effectful `with` expressions, and
value-position reductions remain loud. The `array_reduction_statements` fixture
supplies the self-check differential row and Lean receipt; the pinned oracle
agrees with its `PASS` transcript.

The 22,059-path census remains **5,240 clean / 16,752 partial** (67 include
skips), with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**277/272/0/5 → 278/273/0/5** and grammar coverage remains **217/92/125**.

## Discarded time-scale metadata queries — 2026-10-26

Valid `$timeunit` and `$timeprecision` calls in statement position now erase
their discarded signed exponent after the existing converter reads a literal
`` `timescale `` directive. Missing or malformed metadata and value uses remain
loud. The `time_scale_statements` fixture supplies the differential row and
Lean receipt; the pinned self-check oracle agrees with its PASS transcript. The
22,059-path census remains **5,240 clean / 16,752 partial** (67 include skips),
with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**267/262/0/5 → 268/263/0/5** and grammar coverage remains **217/92/125**.

## Discarded integral signing casts — 2026-10-26

Valid `$signed` and `$unsigned` calls in statement position now erase their
discarded integral result after the existing signing converter checks arity,
width, and operand purity. Real, aggregate, malformed, and effectful operands
remain loud. The `signing_statement` fixture supplies the differential row and
Lean receipt; the pinned self-check oracle agrees with its PASS transcript. The
22,059-path census remains **5,240 clean / 16,752 partial** (67 include skips),
with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**266/261/0/5 → 267/262/0/5** and grammar coverage remains **217/92/125**.

## Discarded constant `$clog2` queries — 2026-10-26

An admitted `$clog2` call in statement position now erases its discarded
result. The existing converter still checks the operand and leaves malformed,
effectful, and otherwise unsupported calls loud. The `clog2_statement` fixture
covers literal and constant-parameter operands; Icarus agrees with the PASS
transcript. The 22,059-path census remains **5,240 clean / 16,752 partial**
(67 include skips), with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**265/260/0/5 → 266/261/0/5** and grammar coverage remains **217/92/125**.

## Discarded bounded `$isunbounded` queries — 2026-10-26

A literal or bounded-parameter `$isunbounded` call in statement position now
erases its discarded one-bit result. IEEE 1800-2023 §6.20.7 makes these values
known bounded rather than the special `$` value; ordinary variables, unbounded
parameters, malformed calls, and value uses remain loud. The
`isunbounded_statement` fixture covers both literal and parameter forms. The
22,059-path census remains **5,240 clean / 16,752 partial** (67 include skips),
with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**; differential coverage grows
**264/259/0/5 → 265/260/0/5** and grammar coverage remains **217/92/125**.

## Discarded time-zero realtime query — 2026-10-26

The zero-argument `$realtime` call now erases when its real result is discarded
at time zero. Argumented, delayed, and value-returning forms remain loud
because the tier has no general real-time state. The `realtime_query_statements`
fixture covers the statement form. The 22,059-path census remains **5,240
clean / 16,752 partial** (67 include skips), with `AssignmentExpression:target`
at **2,853**; differential coverage grows **263/258/0/5 → 264/259/0/5** and
grammar coverage remains **217/92/125**.

## Discarded time-zero integer queries — 2026-10-26

Zero-argument `$time` and `$stime` calls in statement position now erase their
discarded result using the existing exact time-zero literal rule. Argumented,
delayed, and value-returning forms remain loud. The `time_query_statements`
fixture covers both calls. The 22,059-path census remains **5,240 clean /
16,752 partial** (67 include skips), with `AssignmentExpression:target` at
**2,853**; differential coverage grows **262/257/0/5 → 263/258/0/5** and
grammar coverage remains **217/92/125**.

## Discarded fixed dimension queries — 2026-10-26

Valid fixed-type `$size`, `$high`, `$left`, `$right`, `$low`, `$increment`,
`$dimensions`, and `$unpacked_dimensions` calls in statement position now
erase their discarded result after the existing elaborated-metadata query
proves the shape. Dynamic arrays, dynamic selectors, effectful operands, and
value uses remain loud. The `dimension_query_statements` fixture covers all
eight calls. The 22,059-path census remains **5,240 clean / 16,752 partial**
(67 include skips), with `AssignmentExpression:target` at **2,853**;
differential coverage grows **261/256/0/5 → 262/257/0/5** and grammar
coverage remains **217/92/125**.

## Discarded literal bit queries — 2026-10-26

Valid discarded literal-operand `$countbits`, `$countones`, `$onehot`,
`$onehot0`, and `$isunknown` calls now erase without a represented state
effect. Dynamic operands stay loud because these queries must evaluate them;
the `literal_bit_query_statements` fixture covers all five forms. The
22,059-path census remains **5,240 clean / 16,752 partial** (67 include
skips), with `ExpressionStatement:CallExpression` at **2,775**; differential
coverage grows **260/255/0/5 → 261/256/0/5** and grammar coverage remains
**217/92/125**.

## Discarded `$bits` does not evaluate its expression — 2026-10-26

Valid one-argument `$bits(expr)` calls in statement position now erase without
evaluating `expr`, matching IEEE 1800-2023 §20.6.2. The `bits_discarded`
fixture proves that a post-increment argument stays at zero; value-returning,
malformed, and other stateful calls remain loud. The 22,059-path census remains
**5,240 clean / 16,752 partial** (67 include skips), with
`ExpressionStatement:CallExpression` at **2,775** because the corpus has no
standalone discarded `$bits` witness; differential coverage grows
**259/254/0/5 → 260/255/0/5** and grammar coverage remains **217/92/125**.

## Discarded `$typename` does not evaluate its expression — 2026-10-26

Valid one-argument `$typename(expr)` calls in statement position now erase
without evaluating `expr`, matching IEEE 1800-2023 §20.6.1. The
`typename_discarded` fixture proves that a post-increment argument stays at
zero; value-returning, malformed, and other stateful calls remain loud. The
22,059-path census remains **5,240 clean / 16,752 partial** (67 include skips),
with `ExpressionStatement:CallExpression` at **2,775** because the corpus has
no standalone discarded `$typename` witness; differential coverage grows
**258/253/0/5 → 259/254/0/5** and grammar coverage remains **217/92/125**.

## Literal predefined-stdout position errors — 2026-10-26

The exact `$ftell(32'h8000_0001)` query on the predefined stdout descriptor
now lowers to the IEEE error result, signed 32-bit `-1`, while a discarded
call is inert because the self-check state has no seekable file object. Dynamic
descriptors and file-position state remain loud. The `ftell_stdout_error`
fixture and Lean receipt pin the result. The 22,059-path census remains
**5,240 clean / 16,752 partial** (67 include skips), with `CallExpression` at
**2,771** because the corpus has no exact predefined-stdout `$ftell` witness;
differential coverage grows **257/252/0/5 → 258/253/0/5** and grammar coverage
remains **217/92/125**.

## Literal predefined-stdout seek errors — 2026-10-26

The exact `$fseek(32'h8000_0001, 0, 0)` query on the predefined stdout
descriptor now lowers to the IEEE error result, signed 32-bit `-1`, while a
discarded call is inert because the self-check state has no seekable file
object. Dynamic descriptors, offsets, whence values, and other file operations
remain loud. The `fseek_stdout_error` fixture and Lean receipt pin the result.
The 22,059-path census moves **5,239 → 5,240 clean** and **16,753 → 16,752
partial** (67 include skips), with `CallExpression` falling **2,772 → 2,771**;
differential coverage grows **256/251/0/5 → 257/252/0/5** and grammar coverage
remains **217/92/125**.

## Literal coverage queries in the empty database — 2026-10-26

The self-check surface now lowers literal-only `$coverage_control`,
`$coverage_get`, `$coverage_get_max`, `$coverage_merge`, and `$coverage_save`
calls to signed 32-bit `SV_COV_NOCOV` zero. The model has no coverage database,
covergroup counters, or external coverage state, so dynamic scopes and source
coverage constructs stay loud. The `coverage_nocov_queries` fixture covers all
five calls and their zero results. The 22,059-path census measures **5,239
clean / 16,753 partial** (67 include skips); `CallExpression` falls **2,778 →
2,772**, differential coverage is **256/251/0/5**, and grammar coverage remains
**217/92/125**.

## Pure conditional continuous drivers from literal source state — 2026-10-26

Whole packed-net drivers with literal arms and one direct literal
initialization for each condition now snapshot their selected arm before the
existing static per-bit resolver. Unknown, changing, effectful,
strength-sensitive, and scheduler-visible forms remain loud because they need
the kernel's live driver path. The `continuous_conditional_history_drivers`
fixture and the `wire_z_z_resolves_to_z` / `net_decl_assign_one_per_net_v4`
corpus witnesses cover the admitted shape. The 22,058-path census moves
**5,231 → 5,233 clean** and **16,760 → 16,758 partial**;
`AssignmentExpression:target` falls **2,855 → 2,853**; differential coverage
is **255/250/0/5** and grammar coverage remains **217/92/125**.

## Selected continuous windows from one literal source write — 2026-10-26

Fixed packed-net windows whose source variable has one direct literal
initialization now snapshot that source before the existing static per-bit
resolver. Dynamic, multiply-written, effectful, and strength-sensitive drivers
remain loud because they need the kernel's live continuous-driver path. The
`continuous_selected_history_windows` fixture and the
`scalared_net_allows_bitselect` corpus witness cover the admitted source-bound
shape. The 22,058-path census moves **5,230 → 5,231 clean** and
**16,761 → 16,760 partial**, while `AssignmentExpression:target` falls
**2,856 → 2,855**; differential coverage is **254/249/0/5** and grammar
coverage remains **217/92/125**.

## Dynamic noncanonical packed indexed slices — 2026-10-26

Dynamic `+:` and `-:` part-selects on noncanonical one-bit packed vectors now
reuse the flat selected-read/write evaluator after normalizing the runtime
base label. Ascending declarations map each slice to an increasing flat
window, while descending declarations retain the evaluator's indexed direction
convention. The pure signed 32-bit base restriction remains. Effectful,
unsigned, aggregate, and unsupported forms stay loud; partial reads retain the
selected evaluator boundary. The
`packed_array_dynamic_part_select` fixture covers both directions and their
read/write aliasing.

The refreshed **22,058-path** census remains **5,230 clean / 16,761 partial**
(67 include skips), with `AssignmentExpression:target` at **2,856**; this
fixture shape is absent from the corpus. Differential coverage grows
**251/246/0/5 → 252/247/0/5** with no disagreements, and grammar coverage
remains **217/92/125**.

## Dynamic indexed slices over wide packed elements — 2026-10-26

Dynamic `+:` and `-:` slices over nested packed arrays now scale the runtime
outer label by the packed inner-element width before entering the existing
selected-read/write evaluator. Widths are admitted in whole inner-element
chunks; ascending slices use an increasing flat window and descending slices
retain the evaluator's high-endpoint convention. Effectful bases, aggregate
receivers, and unsupported forms stay loud. The
`packed_array_dynamic_wide_slice` fixture and Lean receipt cover both range
directions and read/write aliasing.

The refreshed **22,058-path** census remains **5,230 clean / 16,761 partial**
(67 include skips), with `AssignmentExpression:target` at **2,856**; this
fixture shape is absent from the corpus. Differential coverage grows
**252/247/0/5 → 253/248/0/5** with no disagreements, and grammar coverage
remains **217/92/125**.

## Dynamic noncanonical packed-element targets — 2026-10-26

Blocking assignments to dynamic elements of noncanonical one-bit packed vectors
now reuse the declared-label normalizer already used by packed reads. An
ascending target such as `a[i]` for `logic [0:7] a` maps `i` from the declared
right label into the flat vector offset, preserving read/write aliasing and the
existing signed 32-bit index boundary. Unsigned, effectful, aggregate, and
unsupported selectors remain loud. The `packed_array_dynamic_target` fixture
and differential row cover the admitted ascending target.

The refreshed **22,058-path** census remains **5,230 clean / 16,761 partial**
(67 include skips), with `AssignmentExpression:target` at **2,856** because
the corpus has no target-only instance of this shape. Differential coverage
grows **250/245/0/5 → 251/246/0/5** with no disagreements, and grammar
coverage remains **217/92/125**.

## Dynamic nested packed-element indexing — 2026-10-26

A dynamic element select on a nested packed array with integral elements now
normalizes the declared label into the existing flat-vector representation by
scaling the runtime outer index by the packed element width. Reads and
blocking targets share the lowering, and ascending and descending declared
ranges use their right-hand label as the offset origin. Out-of-range values
retain the selected-read/write behavior; aggregate, effectful, nonintegral,
and unsupported index forms remain loud. The `packed_array_dynamic_index`
fixture and differential row cover the read/write aliasing path, while the
multidimensional extractor tests pin the offset geometry.

The refreshed **22,058-path** census moves **5,227 → 5,230 clean** and
**16,764 → 16,761 partial** (67 include skips). `AssignmentExpression:target`
falls **2,857 → 2,856** and `ElementSelectExpression:source-type` falls
**479 → 476**; `CallExpression` remains **2,778**. Differential coverage grows
**249/244/0/5 → 250/245/0/5** with no disagreements, and grammar coverage
remains **217/92/125**.

## Packed-array packed-struct member windows — 2026-10-26

Constant element selections of packed arrays whose elements are untagged
packed structs or unions now share the existing flat vector representation.
The extractor composes the declared packed-array element offset with the
selected field's bit offset, so reads and blocking writes through forms such as
`arr[0].hi` observe the same storage. Dynamic selectors, tagged aggregates,
and nonintegral members remain loud. The `packed_array_struct_member` fixture
and differential row exercise the admitted form; extractor regressions cover
the dynamic boundary.

The refreshed **22,055-path** census moves **5,166 → 5,168 clean** and
**16,822 → 16,820 partial** (67 include skips). `AssignmentExpression:target`
falls **2,875 → 2,873** and `MemberAccessExpression` **1,019 → 1,018**;
`CallExpression` remains **2,801**. Differential coverage grows
**219/214/0/5 → 220/215/0/5** with no disagreements, and grammar coverage
remains **217/90/127**.

## Packed-union reshaped member windows — 2026-10-26

Constant element and part selections chained through an untagged packed-union
member now compose every fixed offset into one `SelectRead` or `SelectTarget`
window. This covers reshaped views such as `value.lanes[0][2:1]` while keeping
dynamic selectors, overlapping continuous drivers, tagged aggregates, and
nonintegral members loud. The `packed_union_reshaped_member` fixture and
differential row exercise the aliasing behavior; extractor regressions retain
the dynamic and overlap boundaries.

The refreshed **22,055-path** census moves **5,168 → 5,169 clean** and
**16,820 → 16,819 partial** (67 include skips). `AssignmentExpression:target`
falls **2,873 → 2,872**; `CallExpression` remains **2,801**. Differential
coverage grows **220/215/0/5 → 221/216/0/5** with no disagreements, and
grammar coverage remains **217/90/127**.

## Fixed-array fields inside unpacked structs — 2026-10-26

Unpacked structs may now contain finite fixed unpacked arrays of scalar or
packed-integral leaves. The legacy flat state emits one cell per declared
array element, and constant or dynamic element writes through the struct
field use those cells; dynamic or aggregate fields remain loud. The
`struct_array_field_windows` fixture and differential row cover declaration,
constant selection, dynamic selection, and readback, with extractor
regressions for the flattened names and guarded writes.

The **22,055-path** census remains **5,169 clean / 16,819 partial** (67 include
skips); `AssignmentExpression:target` shifts **2,872 → 2,869** while the
files using this shape retain independent unsupported constructs. Differential
coverage grows **221/216/0/5 → 222/217/0/5** with no disagreements, and grammar
coverage remains **217/90/127**.

## Fixed-array field assignment patterns — 2026-10-26

Exact positional assignment patterns can now write a finite fixed unpacked
array field inside an unpacked struct. The pattern is expanded into the
field's existing flattened cells, preserving source-before-destination
sampling and two-state conversion; dynamic, partial, aggregate, and aliased
patterns remain loud. The `struct_array_field_pattern` fixture and
differential row cover the admitted form, with extractor regression coverage
for the member-path lowering.

The **22,055-path** census moves **5,169 → 5,171 clean / 16,819 → 16,817
partial** (67 include skips); `AssignmentExpression:target` falls **2,869 →
2,867**. Differential coverage grows **222/217/0/5 → 223/218/0/5** with no
disagreements, and grammar coverage remains **217/90/127**.

## Struct array-field default patterns — 2026-10-26

Keyed and `default` assignment patterns now recurse through finite fixed
unpacked array fields inside untagged unpacked structs. Each array element is
expanded in declaration order into the existing flat cells, preserving
two-state conversion and rejecting patterns that read the destination while
it is being sampled. The `struct_array_field_default` fixture and differential
row cover both whole-default and keyed-default forms; dynamic and aliased
aggregate patterns remain loud.

The capped **22,055-path** census moves **5,171 → 5,174 clean / 16,817 →
16,814 partial** (67 include skips); `AssignmentExpression:target` falls
**2,867 → 2,862**. Differential coverage grows **223/218/0/5 → 224/219/0/5**
with no disagreements, and grammar coverage remains **217/90/127**.

## Struct array-field enum type-key defaults — 2026-10-26

Nested enum type-key patterns now lower through fixed unpacked array fields in
untagged unpacked structs. Enum leaves use the existing declared-value pattern
converter while scalar default leaves retain their normal width and signedness;
other aggregate leaf shapes remain loud. The
`struct_array_field_enum_default` fixture and differential row cover the
recursive enum/default form, with extractor regression coverage for the cell
names and values.

The capped **22,055-path** census moves **5,174 → 5,175 clean / 16,814 →
16,813 partial** (67 include skips); `AssignmentExpression:target` falls
**2,862 → 2,861**. Differential coverage grows **224/219/0/5 → 225/220/0/5**
with no disagreements, and grammar coverage remains **217/90/127**.

## Finite literal dynamic-array reductions — 2026-10-26

Finite dynamic arrays initialized by positional integral literal patterns now
sample their elements into the existing flat cells. The established `sum`,
`product`, `and`, `or`, and `xor` reductions then fold those cells with their
intrinsic element or `with` width. Uninitialized, resized, keyed/default,
effectful, aggregate, and nonintegral dynamic arrays remain loud. The
`dynamic_array_reductions` fixture and differential row cover all five
methods, with extractor regressions for initialization, lowering, and the
uninitialized boundary.

The capped **22,056-path** census moves **5,175 → 5,192 clean / 16,813 →
16,797 partial** (67 include skips); `VariableSymbol:2state` falls **2,285 →
2,223** and `ExpressionStatement:CallExpression` falls **2,777 → 2,776**.
`AssignmentExpression:target` remains **2,861** and `CallExpression` remains
**2,801**. Differential coverage grows **225/220/0/5 → 226/221/0/5** with no
disagreements; grammar coverage remains **217/90/127**.

## Nested finite fixed-array reductions — 2026-10-26

Finite nested unpacked arrays can reduce one dimension when a pure `with`
expression recursively reduces each row to an integral scalar. The lowering
binds each row to its flat storage prefix, so both `item.sum` and
`item.sum with (item)` preserve the actual iterator binding. Aggregate,
effectful, and non-finite storage shapes remain explicit refusals. The
`nested_2d_reductions` fixture and differential case exercise both forms.

The capped **22,056-path** census moves **5,192 → 5,195 clean / 16,797 →
16,794 partial** (67 include skips). Differential coverage grows **226/221/0/5
→ 227/222/0/5** with no disagreements; grammar coverage remains
**217/90/127**.

## Empty dynamic-array reductions — 2026-10-26

Untouched default-empty dynamic arrays now admit scalar `sum()` and
`product()` reductions, both producing the specified zero identity. Any
resize, write, element selection, effectful `with`, or other reduction stays
loud. The `empty_array_reductions` fixture and differential case cover both
methods.

The capped **22,056-path** census moves **5,195 → 5,197 clean / 16,794 →
16,792 partial** (67 include skips). Differential coverage grows **227/222/0/5
→ 228/223/0/5** with no disagreements; grammar coverage remains
**217/90/127**.

## Dynamic-array struct-field reductions — 2026-10-26

Finite dynamic arrays of untagged unpacked structs now admit pure reductions
whose `with` expression selects one integral field. The row iterator resolves
to the existing flattened field cell; whole structs, aggregate fields, and
iterator-index queries remain loud. The `dynamic_struct_reduction` fixture and
differential case cover the admitted form.

The capped **22,056-path** census moves **5,197 → 5,198 clean / 16,792 →
16,791 partial** (67 include skips). Differential coverage grows **228/223/0/5
→ 229/224/0/5** with no disagreements; grammar coverage remains
**217/90/127**.

## Dynamic-array iterator-index reductions — 2026-10-26

Pure reductions over a finite sampled dynamic array now lower `item.index()`
to each cell's zero-based position. The ordinary scalar width and signedness
remain in force, while dynamic or unrelated iterator calls remain loud. The
`dynamic_array_index_reduction` fixture and differential case cover the form.

The capped **22,056-path** census moves **5,198 → 5,199 clean / 16,791 →
16,790 partial** (67 include skips). Differential coverage grows **229/224/0/5
→ 230/225/0/5** with no disagreements; grammar coverage remains
**217/90/127**.

## Invalid literal `$fopen` modes — 2026-10-26

`$fopen` with a literal path and an invalid literal mode now lowers to the
standard zero descriptor without touching the filesystem. Valid modes,
existence-dependent paths, and dynamic arguments remain loud. The
`fopen_invalid_mode` fixture and differential case cover the deterministic
form.

The capped **22,056-path** census moves **5,199 → 5,200 clean / 16,790 →
16,789 partial** (67 include skips); `CallExpression` falls **2,801 → 2,796**.
Differential coverage grows **230/225/0/5 → 231/226/0/5** with no
disagreements; grammar coverage remains **217/90/127**.

## Semaphore zero-key methods — 2026-10-24

The self-check surface now admits `semaphore.put(0)` and `semaphore.get(0)`
when the handle has a preceding constructor assignment. IEEE 1800-2023
§15.3.2–15.3.3 defines both calls as state-free: `put(0)` returns no keys and
`get(0)` acquires none and cannot block. Literal zero is required and an
unproven or dynamic handle/count remains a loud call boundary. The
`semaphore_zero_key_methods` fixture and differential row exercise both
methods.

The fresh 22,049-file census moves **4,840 → 4,841 clean** and **17,143 →
17,142 partial**; `ExpressionStatement:CallExpression` falls **2,985 →
2,984**. The differential matrix grows **139 → 140 rows** with the new row
matching its declared `PASS` output and no disagreements. Grammar coverage is
unchanged at **214 witnesses, 83 MATCH, and 131 REFUSE**.

## Unobserved literal queue writes — 2026-10-24

The self-check surface now erases a blocking assignment of a queue built only
from scalar literals when the queue has no later source occurrence. Queue
storage is outside the flat state, so this write is unobservable at the end of
the initial block and can be dropped exactly. A later read or method, a
dynamic/effectful element, or a nonblocking write keeps the existing loud
`AssignmentExpression:target` boundary. The `unobserved_queue_literal_write`
fixture and differential row exercise the admitted shape.

The 22,049-file corpus census is unchanged at **4,841 clean**, **17,142
partial**, and **66 include skips** because no sv-tests-2 file has this
unobserved-only queue shape. Differential coverage grows **140 → 141 rows**
with **137 matches, 0 disagreements, and 4 refusals**; grammar coverage stays
at **214 witnesses, 83 MATCH, and 131 REFUSE**.

## Shallow unpacked integral structs — 2026-10-22

The self-check surface now admits an untagged unpacked struct when every direct
field is an integral scalar or packed vector. Ingestion flattens the fields into
ordinary vector cells, and direct member reads, writes, and compound assignments
reuse the existing identifier evaluator. Two-state field initialization and
assignment squashing remain intact. Whole-struct operations, nonintegral or
array fields, tagged structs, and aggregate initializers stay loud because
the legacy state has no aggregate storage. The authored
`unpacked_struct_integral_fields` fixture and differential row exercise the
admitted shape.

The fresh sv-tests-2 census moves **4,378 → 4,409 clean** and **17,601 → 17,570
partial** with zero extraction errors. The leading `VariableSymbol:2state`
blocker falls **5,650 → 5,556**, `AssignmentExpression:target` falls
**3,961 → 3,922**, and `MemberAccessExpression` falls **1,188 → 1,052**.

## Unpacked struct aggregate initializers — 2026-10-22

Positional and complete keyed/default assignment patterns on shallow untagged
unpacked structs are now lowered field by field. Each direct integral field
keeps the existing vector cell, width conversion, and two-state `Squash2`
semantics; pyslang's elaborated field order makes keyed syntax independent of
source key order. Partial, effectful, nested, and nonintegral aggregate forms
remain loud because the representation still has no aggregate slot. The
`unpacked_struct_initializers` fixture covers positional and keyed forms,
including four-state input into a two-state field.

The fresh census moves **4,409 → 4,413 clean** and **17,570 → 17,566
partial**, with zero extraction errors. `VariableSymbol:2state` falls
**5,556 → 5,551**; the differential matrix is now **19 rows, 15 matches, 0
disagreements, and 4 recorded refusals**. Grammar coverage remains **192
witnesses, 60 MATCH, and 132 REFUSE**.

## Unpacked array concatenation initializers — 2026-10-22

Finite unpacked-array declaration initializers may now concatenate constant
array operands, exact typed array patterns, and integral scalar elements. The
extractor expands each operand in declared index order, samples source arrays
before publishing destination cells, and preserves per-cell width and
two-state conversion. Runtime array reads, self-aliasing, mismatched widths,
and nonconstant or effectful operands remain loud. The
`unpacked_concat_initializer` fixture is the differential witness.

On the available 22,035-file corpus snapshot, clean files move **4,413 →
4,414** and partial files **17,556 → 17,555**; `VariableSymbol:2state` falls
**5,548 → 5,547**. The differential matrix adds one matching row with no
disagreements; grammar coverage remains **192 witnesses, 60 MATCH, and 132
REFUSE**.

## Nested unpacked integral structs and arrays — 2026-10-22

Untagged unpacked structs now flatten recursively when all leaves are integral
scalars or packed vectors. Fixed unpacked arrays compose the same lowering over
their constant positions, producing cells such as `values[1].meta.count` and
preserving zero-start and two-state conversion; constant member reads and
writes reuse the flattened member path. Whole struct values, aggregate array
initializers, nonintegral fields, and dynamic selections remain loud. The
`unpacked_struct_array` fixture is the differential witness.

The available 22,035-file snapshot moves clean files **4,414 → 4,416** and
partial files **17,555 → 17,553**; `VariableSymbol:2state` falls **5,532 →
5,521** and `MemberAccessExpression` **1,037 → 1,023**. The differential
matrix adds one matching row with no disagreements; grammar coverage remains
**192 witnesses, 60 MATCH, and 132 REFUSE**.

## Inert module event declarations — 2026-10-22

A module-scope named `event` declaration with no use in the time-zero
self-check path is now admitted as inert metadata. It does not enter the flat
vector state, while event waits, triggers, and other scheduler interactions
remain loud. The `event_declaration` fixture is the differential witness.

The available 22,035-file snapshot moves clean files **4,416 → 4,419** and
partial files **17,553 → 17,550**; `VariableSymbol:2state` falls **5,521 →
5,276**. The differential matrix adds one matching row with no disagreements;
grammar coverage is **193 witnesses, 61 MATCH, and 132 REFUSE**.

## Inert module real declarations — 2026-10-22

A module-scope `real` or `shortreal` declaration with no use in the time-zero
self-check path is now admitted as inert metadata. It does not enter the flat
vector state; floating-point reads, writes, arithmetic, and formatting remain
loud. The `real_declaration` fixture is the differential witness.

The available 22,035-file snapshot moves clean files **4,419 → 4,421** and
partial files **17,550 → 17,548**; `VariableSymbol:2state` falls **5,276 →
4,990**. The differential matrix adds one matching row with no disagreements;
grammar coverage is **194 witnesses, 62 MATCH, and 132 REFUSE**.

## Inert chandle declarations — 2026-10-22

Module-scope and declaration-only local `chandle` variables are now admitted
as inert metadata on the time-zero self-check path. They do not enter the flat
vector state; handle reads, writes, and cross-type assignments remain loud. The
`chandle_declaration` fixture is the differential witness.

The available 22,035-file snapshot moves clean files **4,421 → 4,423** and
partial files **17,548 → 17,546**; `VariableSymbol:2state` falls **4,990 →
4,954**. The differential matrix adds one matching row with no disagreements;
grammar coverage is **195 witnesses, 63 MATCH, and 132 REFUSE**.

## Null virtual-interface declarations — 2026-10-22

A module-scope virtual-interface variable initialized to `null` is now admitted
as inert metadata on the time-zero self-check path. It does not enter the flat
vector state; non-null interface handles, reads, writes, and interface
operations remain loud. The `virtual_interface_null_declaration` fixture is the
differential witness.

The available 22,035-file snapshot moves clean files **4,423 → 4,424** and
partial files **17,546 → 17,545**; `VariableSymbol:2state` falls **4,954 →
4,952**. The differential matrix adds one matching row with no disagreements;
grammar coverage is **199 witnesses, 67 MATCH, and 132 REFUSE**.

## Inert string declarations — 2026-10-22

Module-scope and declaration-only local `string` variables are now admitted as
inert metadata on the time-zero self-check path. They do not enter the flat
vector state; string reads, writes, concatenation, and formatting remain loud.
The `string_declaration` fixture is the differential witness.

The available 22,035-file snapshot moves clean files **4,424 → 4,427** and
partial files **17,545 → 17,542**; `VariableSymbol:2state` falls **4,952 →
4,135**. The differential matrix adds one matching row with no disagreements;
grammar coverage remains **199 witnesses, 67 MATCH, and 132 REFUSE**.

## Nested unpacked-struct initializers — 2026-10-23

Complete assignment patterns for unpacked struct trees now flatten recursively
into leaf cells. Positional, keyed, and default values are converted at each
leaf width with ordinary two-state squashing; partial, effectful, nonintegral,
and aggregate-array forms remain loud. The `nested_struct_initializers` fixture
is the differential witness.

The available 22,035-file snapshot moves clean files **4,427 → 4,429** and
partial files **17,542 → 17,540**; `VariableSymbol:2state` falls **4,135 →
4,133**. The differential matrix adds one matching row with no disagreements;
grammar coverage remains **199 witnesses, 67 MATCH, and 132 REFUSE**.

**Proof inventory, with comments excluded.** There are **98 named
theorems and 10 anonymous examples** in `LeanModels/Sv`, and **121
theorems and 6 examples** in the SV example directories: **235 actual
declarations**, not 235 distinct claims. Spec restatements and their
proof-module counterparts count separately. Oracle constructions that
carry permutation proofs are not added to this declaration count. The
old line-regex count includes one doc-comment line in `Surface.lean`
and six example-header lines; comments must not count as theorems.
A comment/string-aware source scan finds no `sorry`, `admit`, new
`axiom`, `native_decide` or `bv_decide` identifiers in this estate; that
scan is not a fresh kernel-axiom audit.

The six M0 fixtures have functional, trace or race theorems anchored to
their real envelopes by elaboration-time AST equality checks. The three
CV32E40P ingestion examples establish successful-instance `WFNames`
and concrete execution guards, not a functional division theorem.
`Step.lean` proves that non-suspending process stepping agrees with the
self-check statement evaluator. By contrast, `Adequacy.lean` only
defines `CycleAdequacy`: **the whole cycle-to-region compilation
adequacy theorem is still outstanding**. `Load.lean` does not yet load
continuous assignments or combinational processes, and Design2 is not
connected to that loader. New surface work must not assume those
bridges already exist.

**The current surface boundaries are not interchangeable.** M0 has
packed four-state expressions, identifier assignment, `if`/blocks and
its cycle-level process fragment; general loops, calls, classes and
hierarchy remain absent. Design2 adds selected reads/writes, case,
reductions, resizing, signed comparisons, multiplication, integral division,
integral remainder and integral power, but nonconstant shifts are not admitted merely because
their constant expressions can be folded. The self-check vocabulary
adds local declarations, `for`/`repeat` and output/termination tasks. Its
time-zero runner remains initial-only and does not inherit Design2's selected
targets or case statements; the scheduler-facing timed loader is a separate
path and currently admits retained `initial`, plain `always`, and canonical
positive-edge bodies. Extractor, ingestion,
evaluator and kernel-loader refusal inventories must therefore stay separate.

## Simple immediate assertion actions — 2026-10-20

IEEE §16.3 simple immediate assert/assume/cover now compile to the existing
conditional executor with source-kind provenance. Conditions evaluate once;
selected action tails survive waits. Assert/assume with no failure action
retain a loud implicit-diagnostic branch; unsuccessful cover has no failure
effect. Deferred/concurrent checks, assertion controls, unsupported effects,
symbolic mode and invalid source retain their boundaries. Null failure
actions remain loud pending independent parser agreement. No scheduler changed.
See [the contract](sv-immediate-assertions.md).

The paired 22,035-path census gains **40 clean files** with no losses
(**3,461 → 3,501**). Thirty-five gains match complete configured independent
transcripts under both oracles; four remain runtime refusals and one exposes
the existing `$finish(0)` source-location observation gap. Four authored
runnable sources match, three preserve explicit refusals, and four kernel
theorems bind to actual parsed source bodies.

### Implicit immediate-assertion diagnostics — 2026-10-22

`ImmediateAssertion:implicit-error` remains the omitted-failure-action
boundary. The fresh 22,043-path census records it in 25 files: 22 are
implicit-error-only and three co-occur. Repricing the sole files finds 24
branches: 17 `assert`, seven `assume`, 12 omitted success actions, 12 explicit
success actions, five named assertions, 13 true conditions, one false
condition, two `always` contexts and one `always_comb` context (features
overlap). The branch carries the standard diagnostic obligation, but the
envelope has no portable diagnostic text/status or coverage-observation
contract. It remains an explicit unsupported else node; no diagnostic is
fabricated and no second scheduler is added. See the [immediate assertion
contract](sv-immediate-assertions.md) and read-only instrument
`extractors/sv/immediate_assert_error_reprice.py`.

### Deferred immediate assertions — 2026-10-22

`ImmediateAssertion:deferred` remains the scheduler-region assertion boundary.
The fresh 22,043-path census records it in 52 files: 19 are deferred-only and
33 co-occur. Repricing the sole files finds 27 branches: 17 `assert`, five
`assume`, five `cover`, 16 `#0` Observed-region forms, 11 `final` Postponed-
region forms, 15 single system-call actions, 12 null actions, one block-action
diagnostic, four `always` contexts, one `always_comb` context and one
protected-region form (features overlap). The envelope has no deferred
sampling/re-evaluation, pending-report, action restriction or end-of-simulation
ordering state. No branch is rewritten as an immediate conditional and no
second scheduler is introduced. See the [immediate assertion contract](sv-immediate-assertions.md)
and read-only instrument
`extractors/sv/immediate_assert_deferred_reprice.py`.

## Plain always source repetition — 2026-10-20

Plain `always` (§9.2.2.1) starts at time zero and repeats its complete source
statement through the existing retained loop interface. One source process
becomes one ready process, with no separate rearming carrier. Delay/event
waits retain the current tail and loop boundary. The initial-only runner
still refuses it, and canonical positive-edge encoding is unchanged.
Unsupported sensitivities, unmodelled declaration lifetimes, invalid source,
procedural edge publication and symbolic-mode repetition stay loud.
See [the contract](sv-always.md).

The paired 22,035-path census gains **90 clean files**, with no losses
(**3,371 → 3,461**). Six gains match complete independent transcripts under
both schedule oracles; one exposes a same-time observation race and matches
only the reverse oracle. The remaining 83 are runtime refusals. Four authored
sources match under both oracles; a fifth preserves the edge-publication
boundary. Four kernel theorems bind to actual parsed source bodies.

## Procedural for/repeat (IEEE 1800-2023, 12.7.1–12.7.2 and 12.8)

The legacy/self-check tier retains source-ordered initializers, conditions,
steps and bodies. `for` initializes once; `repeat` samples once. Normal
body completion and `continue` advance the correct phase; `break` exits
the nearest loop. Resumable boundary markers use the existing scheduler
continuation interface without reconstructing an entered loop. The
executor/stepper correspondence covers these phases, and the ordered-header
theorem is anchored to an extracted source fixture.

Three original fixtures confirm the admitted count and transfer behavior.
Repeat counts follow the sampled signed-32-bit conversion (x/z bits become
zero and nonpositive counts execute no body); repeated-body declaration
lifetimes, effectful headers, symbolic loops, and explicit process-control
suspension/rearming remain loud. No cycle-to-region
adequacy extension is claimed by this loop surface. See
`docs/sv-loops.md` for the exact boundary.

## Retained waiting targets (IEEE 1800-2023, 9.7)

The scheduler retains fixed edge sensitivities and absolute delay deadlines
alongside each process residual. Supported waiting-target suspension/resume
desensitizes an edge wait without latching an occurrence; resuming an edge
wait re-sensitizes it, while a due delay is carried into Active at resume.
Ordinary dependency waits preserve the existing continuation and queued NBA
work. Ready-process suspension, level-wait re-entry, terminal/duplicate
suspension, and other process-control branches remain loud until their rules
are independently represented.

See `docs/sv-wait-targets.md` for the admitted boundary and guards.

## Constant procedural delays (IEEE 1800-2023, 9.4)

The scheduler-facing envelope admits a deliberately narrow delay-control
surface: a known nonnegative integral literal `#d` below `2^64`, retaining its
original statement body as a `Delay` node. `elabTimedDesign` admits one or more
`initial` processes, schedules them in Active at time zero in source order, and uses the existing
retained-continuation scheduler to register a positive delay as an absolute
timer. Waking the timer returns the same process to Active with its prior
effects and remaining body; no source prefix is rerun.

This is not a second scheduler and does not claim full timing support. Zero
delay is delivered through the shared Inactive-region path; dynamic,
arithmetic, negative, unknown, real/time-literal,
event-list and other unsupported timing forms remain unsupported. The legacy self-check
runner stays time-zero-only and refuses timed nodes. See `docs/sv-delay.md` and
`Examples/system-verilog/delay/proof.lean` for the executable boundary.

The same retained-continuation path admits a simple nested `@(posedge sig)`,
`@(negedge sig)`, or bare `@(sig)` wait for a 1-bit identifier. It lowers to
`WaitEvent` inside the enclosing block, wakes through the fixed registration,
and leaves the self-check runner loud. A bare signal wait observes every value
change, including an `x`/`z` transition; event lists, `iff`, implicit and
non-identifier event controls remain unsupported. See
`Examples/system-verilog/event/proof.lean` for the executable boundary.

Clocked `AlwaysPosedge` processes use the same public representation already
used by `elabDesign`: an initial `WaitEvent`, the body, and an `arm` copy that
reinstates the wait after each completed body. Plain `always` procedures use
the existing true-condition loop over their complete source body, without a
separate arm; see [the source repetition contract](sv-always.md). `AlwaysComb`,
continuous assigns and other process kinds remain loud in the timed loader.

The paired extraction census compares the same **21,934** source paths:
clean **1,804 → 1,840**, **36 gains**, and **zero losses**. Gains are
chapter 12 (29), chapters 6, 34 and 37 (2 each), and chapter 9 (1).
Seven newly added external corpus paths are counted separately, not as
coverage gains. This is an extraction measurement, not whole-corpus
runtime agreement.

## Integral division (IEEE 1800-2023, 11.4.3 and 11.8.2)

Runtime integral `/` and plain scalar `/=` now use the shared four-state
value core through M0, self-check execution and both symbolic compilers.
Unsigned operands use natural-number division; signed operands truncate
toward zero at their common width. A zero divisor or any x/z operand
produces all x. Mixed-sign contexts divide unsigned bit patterns, and
destination narrowing follows division rather than narrowing its operands.

Symbolic runtime division preserves unfolded operand conversions, including
signed constants, so parameter changes recompute the arithmetic width
instead of reusing a default-width quotient. Comparisons, logical operands
and ternary conditions retain their own self-determined widths. Extracted
families with defaults of both 8 and 16 verify the two directions of width
change against independent simulation. Concatenation, replication,
reduction and sign-cast boundaries also retain their intrinsic sizing.
The `unsigned_division` and
`signed_division` theorems consume real extracted divider expressions and
prove width-parametric `BitVec` quotients for nonzero divisors. Zero and
unknown cases have concrete execution checks, not a weakened bridge to
two-state division.

Measured on the same 21,864 corpus paths: clean extraction rises from
1,731 to 1,764, with 33 newly clean rows and no losses. This path set includes
one additional corpus file since the multiplication measurement; both ends
of this comparison include it. All 33 gains and four public self-check
fixtures agree with independent simulation on output and status. These
admission and selected-execution checks do not claim whole-corpus execution.
Real division and selected compound assignment remain loud;
M0's existing selected-expression and unsigned-narrowing boundaries remain.
The operator and symbolic-sizing contract is `docs/sv-division.md`.

## Integral remainder (IEEE 1800-2023, 11.4.3 and 11.8.2)

Runtime integral `%` and plain scalar `%=` now use the shared four-state
value core through the self-check executor and both symbolic instantiation
paths. Unsigned operands use unsigned remainder; signed operands use the
paired truncation-toward-zero remainder at their common width, so the result
has the dividend's sign. A zero divisor or any x/z operand produces all x.
Mixed-sign contexts use unsigned bit patterns, and destination narrowing
occurs after the remainder operation.

The extractor emits `u%` for unsigned operands and `s%` when both operands
are signed. Symbolic constant positions retain `%` for integer elaboration;
runtime vectors retain the typed operator and the same unfolded
`Resize`/`SignedResize` sizing boundaries as division. The
`unsigned_remainder` and `signed_remainder` theorems consume real extracted
symbolic designs and prove width-parametric `BitVec` remainders for nonzero
divisors. Unknown and zero-divisor rows are checked as all-x, while real and
selected compound targets remain loud.

The focused extractor battery and `remainder_directed` Icarus differential
case cover unsigned, signed, mixed-sign, zero-divisor and unknown operands.
This is a selected operator-family result, not whole-corpus runtime
conformance. The detailed contract is `docs/sv-remainder.md`.

## Integral power (IEEE 1800-2023, 11.4.3, 11.6 and 11.8.1–11.8.2)

Integral `**` now reaches the shared four-state `LVec.pow` rule through the
self-check executor and both symbolic instantiation paths. The base follows
the expression or assignment context width; the exponent remains
self-determined in both width and signedness. Runtime tags record all four
base/exponent signedness combinations, while constant-position `**` keeps
its integer elaboration path.

Known nonnegative exponents use modular repeated squaring at the base width.
Zero exponents produce one, including `0 ** 0`; unknown operands produce
all x. For a negative signed exponent, zero produces all x, one produces
one, signed minus one follows exponent parity, and all other integral bases
produce zero, matching Table 11-4. Real power and unresolved signed-port
boundaries remain loud.

`Examples/system-verilog/power/proof.lean` proves a width-parametric
unsigned power bridge over a real extracted design and checks the signed
negative-exponent cases directly. The three self-check fixtures cover
positive/context sizing, signed base behavior and the standard's
zero-to-negative all-x case. The last case is a documented reference
divergence: IEEE 1800-2023 §11.4.3 Table 11-4 and independent Icarus
execution require all x, while the separate reference run returns zero. It
is therefore not counted as a reference confirmation. Nonzero
negative-exponent disagreements are kept out of newly oracle-confirmed
fixtures pending a separate ruling.

Fresh extraction over the paired 21,934-file corpus rises from 1,764 to
1,804 clean, with 40 gains and no losses; every gain is in chapter 11.
These are admission measurements, not a claim that every clean row executes.
The detailed contract is `docs/sv-power.md`.

## Integral shifts (IEEE 1800-2023, 11.4.10)

Runtime `<<`, `>>`, `<<<` and `>>>` now use the shared four-state shift
primitives in M0, the self-check executor and both symbolic instantiation
paths. Shift amounts are self-determined and unsigned; an unknown amount
produces all x. Left and logical-right overshifts zero-fill, while signed
arithmetic-right overshifts sign-fill. The result width is the left operand
width, so assignment context widens that operand before shifting and the
destination narrows afterward. The extractor records independent signedness
tags for the left operand; the shift amount never controls sign fill.

Plain scalar compound shifts lower to the same typed binary nodes. Selected
targets and invalid frontend compilations remain loud. Constant-position
shifts retain symbolic integer elaboration. `Examples/system-verilog/shifts/`
contains the generated envelope and the width-parametric proof; the detailed
contract is `docs/sv-shifts.md`.

The focused extractor battery has 14 passing tests. On the paired 21,952-file
census, clean extraction rises **2,383 → 2,448** with 65 gains and no losses;
all 65 newly clean rows match the two executable validation paths used for
the measurement. This is a selected-family result, not whole-corpus runtime
conformance.

## Integral multiplication (IEEE 1800-2023, 11.4.3 and 11.8.2)

Runtime `*` reaches the existing four-state `LVec.mul` authority through
M0, the self-check executor, and both symbolic instantiation paths.
The frontend's elaborated operand conversions preserve common-context
sizing: operands extend before multiplication, a wider destination can
retain more product bits, and a narrower destination truncates afterward.
Signed operands sign-extend only in signed contexts; mixed-sign contexts
zero-extend. Any x/z operand collapses the entire result to x, including
`0 * x`; two-state destinations then apply the existing squash conversion.
Plain scalar `*=` shares this operator path; selected compound targets
and division, remainder, power and shifts remain outside this item.

Symbolic constant multiplication retains its integer elaboration and
literal AST shape. Nonconstant symbolic multiplication lowers to the same
runtime operator with common/target operand sizing. The width-parametric
`multiplication_modular` theorem consumes the extracted multiplier's real
expression and proves the `BitVec` modular product at every width.
Four public self-check fixtures cover overflow, widened products,
precedence, signed/mixed-sign extension, unknowns and compound updates.
Invalid frontend compilations carrying admitted products remain loud.

Measured on the same 21,863 corpus paths: clean extraction increases from
1,692 to 1,731, with 39 newly clean rows and no losses. All 39 newly admitted
rows and all four new self-check fixtures agree with independent simulation
on output and status. The extractor battery has 97 passing tests; envelope
regeneration reports 27 live matches, zero divergences and three archived
not-live rows. These are admission and selected-execution measurements,
not a claim that every clean corpus row executes or that the language is
complete. The detailed operator contract is `docs/sv-multiplication.md`.

## Restart validation baseline

**Executed restart checks.** A focused local `lake build` of all 22 SV
modules completes successfully; this is not a claim about every default
repository target. With Python 3.12 and pyslang 11.0.0, the round-trip
gate reports **18 live MATCH** (six `sv-0.1`, twelve `sv-0.2`), zero
divergences and zero timeouts. Three additional archived `sv-0.2`
envelopes refuse because their recorded absolute source paths are absent;
they are not silently counted as fresh or live.

The restart differential measurement selects Icarus explicitly.
A simulator executable's presence is not a simulation verdict:
readiness requires a completed run, not installation detection.

The M0 differential harness verifies **10/10 cases**, including the
race witness that matches the reverse schedule. Phase two verifies
**15 cases and skips one**, `t2_ci`: the installed Icarus rejects that
case-inside fixture at compilation, and no completed alternative run
is established for that restart check. There are zero differential
failures. The phase-two script nevertheless prints "all 16 case(s)
passed" because its summary includes skipped rows; **that summary is
not the measured coverage**. Per-case outcomes, not exit status alone,
are the restart scoreboard. The documentation block check also passes.

### Signed integral breadth — 2026-10-09

The first resumed breadth item is the self-check integral family in
clauses 6 and 11: signed scalar and descending zero-based packed-vector
variables, plus `byte`, `shortint`, `int`, `longint`, `integer` and
`time`, including unsigned variants. Declaration widths, default values
and two-state assignment squashing come from the elaborated type.
Optional signed metadata does not alter legacy unsigned envelopes.

The new `SignedResize` expression lowers to `LVec.resizeSigned`: retain
low bits when narrowing, replicate the exact source sign bit when
widening, including `x` and `z`. Both source and propagated conversion
types must be signed. Mixed-sign expression contexts can instead demand
zero extension; assignment to an unsigned destination can still contain
an inner signed extension. Preserve the frontend's conversion placement,
not merely the destination's declaration. Known negative `%d` and `%0d`
output now uses two's-complement decimal and the existing type-width
padding rule.

`harness/sv/signed_diff_test.py` verifies **six public fixtures, zero
failures and zero skips**, in one Lean batch against explicit Icarus:
predefined widths/defaults, extension and
truncation, signed/mixed-sign comparisons, arithmetic context sizing,
four-state extension and two-state squashing, and decimal formatting.
It also accepts external source lists, while keeping generated envelopes
and logs outside the repository. The CI entry point `./check.sh` delegates
to the existing `tools/ci.sh`; `SV_SIM` selects the phase-two oracle and
defaults to the existing `auto` policy when unset.

The value rule has kernel-checked width and per-bit theorems.
`stepSStmt_done_agrees` relates a completed non-suspending statement
execution to the executor; it is not a new scheduler or a proof that
`CycleAdequacy` has been discharged.

This item does **not** admit symbolic signed widening, reversed packed ranges,
enums/structures/unpacked arrays,
shifts, calls or general loops in the self-check tier. Integral explicit
casts are addressed by the following item.
Its time-zero runner remains initial-only; the separate scheduler-facing
loader admits only the narrow timed `initial` subset documented above. Each
other surface keeps its own admission boundary.

### Signed M0 declarations and relational operators — 2026-10-13

The scheduler-facing M0 envelope admits signed four-state scalar and
descending zero-based packed `logic`/`wire` declarations, including ports.
Declaration and identifier metadata retain `signed: true`; two signed
operands lower order comparisons to `s<`, `s<=`, `s>` and `s>=`. The shared
`LVec` rule compares two's-complement values at each operand width and keeps
the existing all-x result for unknown operands. Unsigned declarations and
operators are unchanged, and symbolic signed widening remains loud.

`Examples/system-verilog/signed_m0/` is a real extracted module whose signed
sum and comparison are checked through the M0 runner and Icarus differential
harness. This is a declaration/operator surface extension, not a scheduler
change.

### Integral wildcard equality — 2026-10-19

`==?` and `!=?` are retained in both envelope schemas and run through one
shared four-state value rule. Right x/z bits are wildcards; a known mismatch
dominates an unknown cared-left bit, and inequality complements the equality
result. Both operators produce an unsigned, one-bit self-determined value.
Both symbolic compilers preserve operand typing and the comparison boundary
inside surrounding arithmetic. The existing Boolean `case inside` selector
also calls the shared rule. No scheduler change is involved.

The paired 22,030-path census gains 29 clean chapter-11 files without losses;
30 files lose wildcard refusals, including one still blocked by `$time`.
The source fixture exercises all scalar pairs, signed/mixed-width and wide
vectors, result extension and nested arithmetic. Source-anchored theorems
cover arbitrary vectors under an all-wildcard right operand. Nonintegral
value/storage types retain their existing refusals. Pure integral membership
is covered by the later §11.4.13 lowering below; symbolic membership remains
loud. See [the operator contract](sv-wildcard-equality.md).

### Unary plus arithmetic — corrected 2026-10-19

Integral unary `+` is retained in both envelope schemas and compiled through
the common `LVec.pos` operator. A known operand is unchanged; any x/z bit
collapses the entire context-sized result to x, as required by IEEE
1800-2023 §11.4.3. The earlier extraction-time identity incorrectly preserved
partially unknown operands. Both symbolic compilers retain the operator,
including their arithmetic-operand sizing paths. Unsupported operand types
and conversions retain their own refusals.

### Unary reductions — 2026-10-13

The legacy M0 surface now admits the six IEEE 1800 reduction operators
(`|`, `&`, `^`, `~|`, `~&` and `~^`) over the existing integral expression
fragment. Each result is a one-bit `Reduce` node. The shared value core folds
the four-state tables once; negated forms apply `Logic.not`, so definite
short-circuiting (`|4'b100x == 1`, `&4'b111x == x`) and unknown propagation are
the same in M0 and the symbolic semantic tier. The `reductions` fixture pins
all six operators against the Icarus differential harness.

`Examples/system-verilog/unary_plus/` is a real extracted module whose
operand, unknown bits and constant unary-plus result are checked by the
independent differential harness. Its arithmetic self-check fixture and
source-anchored known/unknown theorems are described in
`docs/sv-unary-arithmetic.md`.

### Integral variable ports — 2026-10-14

The legacy tier now admits integral variable ports in both directions:
two-state scalar and descending packed types, plus the predefined integer
types, independently of signedness. `Decl.twoState` survives ingestion;
the cycle boundary converts each supplied x/z input bit to zero before
process execution, while absent stimulus entries retain the previous value.
The ordinary `Squash2` node also reaches the M0 evaluator, sharing the
same conversion with the self-check tier. No scheduler is added or changed.

Unconnected inputs in the time-zero runner start z for four-state types and
zero for two-state types; output variables retain their corresponding x/zero
startup. The extracted `integral_ports` design checks signed comparisons,
sign extension, mixed port types and output conversion. Its proof validates
the complete AST against the real envelope before proving input conversion
precedes its first assignment and conversion is idempotent. Width-parametric
startup theorems cover both state counts. Two-state nets, noncanonical packed
ranges, aggregates, and symbolic signed declarations remain loud.
Port defaults and variable initializers are retained rather than silently
dropped. The time-zero runner evaluates them through ordinary declaration
initialization; the connected cycle boundary ignores input defaults and
accepts closed output initializers. Invalid output-net port initializers stay
loud rather than being mistaken for variable startup.

On the same **22,008** corpus paths, extractor-clean rises **2,572 → 2,573**:
two chapter-23 gains, one newly loud negative fixture, four changed refusal sets. The two gains
concern predefined integer port declarations; they do not establish
whole-corpus runtime agreement. The one admission loss rejects a forbidden
output-net port initializer that was previously dropped. `docs/sv-corpus-coverage.md` records the
fresh per-chapter table and `docs/sv-construct-census.json` its generated
summary. The largest residual refusal is assignment targets (4,457 files),
followed by expression calls (4,351), hierarchy (3,833), and two-state
declaration shapes (3,703).

### Two-state declaration boundary — 2026-10-21

The legacy value tier already admits scalar, predefined-integral, packed-vector,
and untagged packed-struct/union two-state variables, with zero startup and
`x`/`z`-to-zero assignment conversion. The fresh corpus's `VariableSymbol:2state`
tag is the remaining mix of unpacked/dynamic/queue/object/event/real/string
declarations and uses. It occurs in 5,744 files, but is the sole refusal in 28;
the common companions are other storage, call, class, and selected-access
boundaries. The symbolic `PDecl` surface now carries `twoState` for the same
unsigned integral scalar and packed-vector shapes, and `Expr2.squash2` applies
the four-state-to-two-state conversion at assignment boundaries. Aggregate,
object, string/real, handle, event, and symbolic signed forms remain loud. The
complete admitted slice and the measured refusal rationale are recorded in
[`sv-two-state-boundary.md`](sv-two-state-boundary.md). No dynamic aggregate,
object, string/real, handle, or event scheduler is smuggled into this rung.

The ordinary portable suite includes x/z stimuli and an absent-input cycle:
all five complete cycle traces agree with both independent simulation and
Icarus. The separate unconnected startup fixture differs: Icarus 13.0
development build `dad78d525` retains z in unconnected two-state input ports,
while independent simulation initializes them to zero. This is recorded as
a simulator divergence, not a model pass. The new integral-variable-port
slice supersedes the older input-port refusal below.

### Nested fixed two-state arrays — 2026-10-22

Bounded fixed-size unpacked arrays with two or more dimensions now lower to
independent vector cells when their leaf type is integral. Constant element
selections reuse those names, so ordinary reads, writes, two-state zero startup,
and x/z-to-zero conversion retain the existing vector semantics. Exact
positional and recursively replicated patterns are flattened in declared range
order; effectful or shape-mismatched patterns, dynamic or queue arrays,
nonintegral leaves, and nonconstant selections remain loud. The
`fixed_array_2state` fixture checks a write/read pair and an untouched cell;
`fixed_array_pattern_2state` checks nested replication. Multidimensional
packed integral leaves remain one vector cell, with packed bit order preserved;
`fixed_array_packed_leaf_2state` checks that form.

The fresh 22,045-path census moves clean files **4,326 → 4,345** and partial
files **17,653 → 17,634**. `VariableSymbol:2state` falls **5,744 → 5,666**;
`AssignmentExpression:target` falls **4,032 → 3,982** as the newly admitted
constant nested selections stop producing target refusals. The differential
matrix has **14 rows, 10 matches, 0 disagreements, and 4 recorded refusals**.

The nested-pattern extension moves clean files **4,347 → 4,351**, partial files
**17,632 → 17,628**, and `VariableSymbol:2state` **5,666 → 5,660**. Its
differential matrix has **16 rows, 12 matches, 0 disagreements, and 4 recorded
refusals**.

The packed-leaf extension moves clean files **4,351 → 4,378**, partial files
**17,628 → 17,601**, `VariableSymbol:2state` **5,660 → 5,650**, and
`AssignmentExpression:target` **3,980 → 3,961**. Its differential matrix has
**17 rows, 13 matches, 0 disagreements, and 4 recorded refusals**.

### Constant out-of-bounds fixed-array writes — 2026-10-22

The target surface now lowers a fully constant out-of-range write on a fixed
unpacked array to `Empty`, as required by IEEE §7.4.5. The RHS remains subject
to the existing pure expression check, and in-range or dynamic selections keep
their cell/selected-target semantics. `fixed_array_oob` checks the no-op while
the two corpus witnesses exercise module and procedural declarations.

The fresh census moves clean files **4,345 → 4,347** and partial files
**17,634 → 17,632**; `AssignmentExpression:target` falls **3,982 → 3,980**.
The differential matrix is now **15 rows, 11 matches, 0 disagreements, and 4
recorded refusals**.

### Constant `$clog2` calls — 2026-10-14

The runtime admission dated 2026-10-20 below extends this historical tier.

The legacy/self-check extractor now admits pure constant `$clog2` calls
(IEEE 1800-2023 §20.8.1) by folding slang's elaborated result to a signed
32-bit `Literal` carrying `fixed_clog2: true`. Zero and one return zero, and
the argument follows the standard's unsigned treatment (`$clog2(-1)` is 32
for a 32-bit argument). Dynamic, effectful, malformed and nonintegral calls
remain loud; invalid compilations retain a `$clog2:invalid-compilation`
refusal. No value-core or scheduler rule changes.

`Examples/system-verilog/clog2` pins zero, one, powers and non-powers together
with the unsigned-negative boundary. The proof runs the real extracted
envelope through the self-check runner and proves the corresponding `clog2`
boundary values. The existing symbolic `SysCall` vocabulary is unchanged.

On the same **22,008** corpus paths, the fresh extractor census rises
**2,573 → 2,580 clean** with seven gains and no losses, all in chapters 5 and
20. `CallExpression` falls from 4,351 to 4,328 files; the other leading
refusal classes are unchanged. This is extractor admission, not whole-corpus
runtime or simulator agreement.

### Fixed integral dimension queries — 2026-10-14

The initial legacy/self-check slice folded `$size`, `$high`, `$left`, `$right`,
`$low`, `$increment`, `$dimensions` and `$unpacked_dimensions` for fixed
admitted integral declarations (IEEE 1800-2023 §20.7).
Results are signed 32-bit literals carrying `fixed_dimension_query` provenance:
`$size` returns the declared width, `$high`/`$left` return width minus one,
and `$right`/`$low` return zero; `$increment` returns one for the admitted
descending packed dimensions; `$dimensions` returns one and
`$unpacked_dimensions` returns zero. Dynamic/associative/queue dimensions,
effectful operands, malformed calls and nonintegral arguments remain loud;
frontend errors retain a
`DimensionQuery:invalid-compilation` refusal. No interpreter or scheduler
rule changes. These width-derived formulas describe that original
single-dimension slice, not the extension below.

`Examples/system-verilog/dimension_queries` runs the real envelope through the
self-check runner. On the same **22,008** corpus paths, clean extraction rises
**2,580 → 2,588** with eight chapter-20 gains and no losses; `CallExpression`
falls **4,328 → 4,233**.

The scalar dimension-count follow-up admits `$dimensions` and
`$unpacked_dimensions` for the same fixed integral declarations. Clean
extraction rises **2,588 → 2,596** with eight additional gains (one in
chapter 7 and seven in chapter 20), no losses, and `CallExpression` falls
**4,233 → 4,207**. This remains extractor admission, not whole-corpus runtime
or simulator agreement.

### Fixed array dimension selection — 2026-10-19

The same §20.7 family now preserves arbitrary fixed declared packed and
unpacked ranges over integral elements, including ascending, negative and
equal bounds. Dimensions are numbered unpacked before packed; predefined
integers, enums and untagged packed aggregates contribute their implicit bit
dimension.
Plain scalar `bit`/`logic`/`reg` values contribute none: this corrects the
earlier `$dimensions(scalar) = 1` result to zero. Even a one-bit enum still
contributes one dimension; it is not erased to its scalar base type.

The six bound/size/direction queries accept an optional pure, frontend-bound
constant dimension selector, defaulting to one. Literal leaves and parameter
or enum constants also work without a cached evaluation of an unvisited source
branch. No evaluation context is invoked: compound selectors without a bound
constant remain loud, as do runtime selectors, invalid dimensions,
dynamic/associative/queue storage and effectful operands. These
query provenance markers survive outer constant folding and invalid
compilations retain the existing refusal. Fixed metadata-only type aliases
are erased without admitting their runtime storage; rejected compilations
retain `TypeAlias:invalid-compilation`. Tagged unions remain outside this
extension. The runtime and scheduler are unchanged.

The expanded real `dimension_queries` fixture checks the selected bounds,
direction, counts, mixed dimensions, packed aggregates and scalar/enum
distinction through the self-check runner and independently confirmed source
observations. The fresh paired **22,030**-path census changes **2,596 → 2,599
clean** and **19,368 → 19,365 partial**, with **66 includes skipped**,
**0 extraction errors**, three gains and no losses. Two gains are chapter-20
type-operand queries and one is a chapter-6 fixture with an unused fixed
type alias; all three run through the Lean self-check tier and agree with
independent source observations. The **33** files previously carrying
`CallExpression:dimension:arity` no longer carry that refusal. This is not a
claim of whole-corpus runtime coverage. See `docs/sv-corpus-coverage.md` for
the chapter table.

### Two-state output ports — 2026-10-12

The legacy/self-check envelope admits an unsigned scalar or descending
zero-based packed **2-state output** port. Its `two_state` metadata is retained
through ingestion, and an unconnected output starts at zero as required by the
port's 2-state variable semantics. This is a declaration-boundary slice; the
body and output observation still use the existing time-zero runner.

2-state input ports remain loud because an unconnected input is not a faithful
zero source at this tier. Signed 2-state output, 2-state nets, reversed-range,
aggregate and symbolic 2-state forms remain outside the admission. No
scheduler or value-core rule changes are introduced.

### Signed 2-state output ports — 2026-10-13

The self-check declaration slice now also admits a signed `bit` output port.
Its `two_state` and `signed` metadata are retained, startup is zero, and
assignments still squash x/z bits before storage. The fixture
`signed_two_state_output` checks startup, signed comparison and the
four-state-to-two-state assignment conversion; a width-parametric zero-default
theorem anchors the initialization rule. Signed 2-state inputs and nets remain
loud.

### Integral explicit casts — 2026-10-09

The legacy/self-check extractor now lowers integral size, signing and
data-type casts over the scalar, predefined integer and descending
zero-based packed-vector types already admitted by this surface
(clauses 6.24 and 11.7). The operand is self-determined: widening copies
its sign bit when the **operand** is signed, including when the cast's
result type is unsigned. This differs from propagated mixed-sign
arithmetic sizing. Narrowing retains the low bits; equal-width signing
casts preserve the bits while slang carries the result's signedness
into subsequent consumers. A four-state-to-two-state cast applies
`Squash2` after resizing, mapping each `x` and `z` to zero.

No new value operator or scheduler is introduced: the lowering uses
the existing `Resize`, `SignedResize` and `Squash2` expression rules.
Original fixtures in `harness/sv/casts/` exercise dynamic operands,
opposite source/result signedness, nested contexts and unknown bits.
The existing strict differential harness accepts them through its
external source-list option; corpus artifacts and logs remain private.
The actual-fixture proof uses the shared non-suspending step/executor
correspondence, not a cycle-adequacy assumption.

Real/string/enum/structure casts, bitstream/streaming conversions,
unsupported declared ranges and symbolic casts remain loud. This is
not an expansion of the M0 or Design2 loaders' admission boundaries,
nor an implementation of dynamic `$cast`.

### Integral typedef aliases — 2026-10-09

The legacy/self-check extractor admits module and compilation-unit
`typedef` declarations whose bound canonical type is an already-admitted
scalar, predefined integer or descending zero-based packed scalar vector
(clause 6.18). Slang resolves each use before lowering; the declaration
has no runtime effect and is omitted. Alias chains retain the canonical
type's width, signedness and two-state/four-state behavior at declarations,
assignments, operators and casts. Block-local typedefs are already
elaboration-only in the bound statement tree; their variables use the
same existing type admission. This item changes no local-scope admission.

Original fixtures in `harness/sv/typedefs/` cover all three scopes, alias
chains, predefined integer types, signed cast boundaries, same-width
reinterpretation and unknown-bit handling. The actual-fixture proof of
a signed packed typedef uses the shared completed-step/executor rule.
No value node, parser admission rule or scheduler changes are needed.

Structure/union/nonintegral typedef declarations, unpacked arrays and
unsupported packed ranges remain outside this admission. Bound integral
enums are addressed by the following item.
Ports and nets keep their existing independent type restrictions; package
imports, type parameters and forward declarations remain loud. Symbolic
integral typedef declarations remain unsupported; the existing symbolic
enum metadata path is unchanged.

### Bound integral enumerations — 2026-10-09

The legacy/self-check surface admits enumerated types whose bound base
type is an already-admitted scalar, predefined integer or descending
zero-based packed scalar vector (clause 6.19). Slang checks nominal enum
declarations, assignments and casts before lowering. Enum variables retain
their base width, signedness, state domain and default value; their initial
value is not inferred from the first enumerator. Member expressions lower
to the complete bound bit pattern, preserving negative values, automatic
increments, generated member names and four-state `x`/`z` members.

Admitted typedefs and transparent enum-member scope bindings have no
runtime effect and are omitted at module and compilation-unit scope.
Block-local declarations use the existing elaborated type path. Static
casts use the existing source-signed resizing and target-state conversion
rules (clause 6.24), without adding a member-validity check. Enum-bearing
compilations with frontend errors stay loud: erasure must not turn an
illegal implicit assignment, duplicate member or overflow into executable
code. This is an extractor lowering, not a new value domain or scheduler.

Six original fixtures in `harness/sv/enums/` pass independent
differential checks. They cover base
defaults, signed/unsigned values, generated names, unknowns, static casts
and all three typedef scopes. A real-source fixture certificate
and completed-step proof use the unchanged executor correspondence.
Fresh extraction over 21,787 corpus files yields 1,463 clean, 20,294
partial and 30 include-skipped files: 60 previously partial files become
extractor-clean, with no previously clean file regressing. Extractor-clean
is not a claim of valid elaboration, live execution or simulator agreement.

String-valued enum `name()`, dynamic `$cast`, packages/imports, enum ports/nets,
unpacked containers and unsupported base ranges remain loud. Numeric enum
methods are admitted by the 2026-10-20 item below. The symbolic
`sv-0.2` enum identity/metadata path remains unchanged.

### Pure ordinary case statements — 2026-10-10

The legacy/self-check extractor lowers unqualified integral `case`
statements (clause 12.5) into existing `if` branches with exact four-state
`===` comparisons. Slang's bound subject and labels already carry the
common width and signedness determined by the entire case, including
later labels. Lowering preserves that context rather than independently
sizing each comparison. Labels and arms are searched in source order;
the first match executes once. A default is the terminal fallback,
wherever it appeared in the source, and an absent default leaves state
unchanged when no label matches.

Subject and label expressions must be completely admitted by the existing
pure integral expression fragment. Re-evaluation during an unsuccessful
search cannot observe a changed state; calls, assignments, increments and
other effectful or unsupported expressions stay loud, except fixed-size
`$bits` queries whose operands are not evaluated. Nested label tests,
not eager logical disjunctions, preserve first-match search. Six original
fixtures in `harness/sv/ordinary_cases/` pass independent differential checks
for exact `x`/`z`, multiple labels, defaults, whole-case sizing and runtime
expressions. No value type, interpreter, process rule or scheduler changes.
Fresh extraction admits 54 previously partial simulation files without
losing a previously clean file: 1,517 clean, 20,240 partial and 30
include-skipped out of 21,787. These are extractor-only measurements,
not corpus-wide reference or runtime coverage.

Qualified `unique`/`unique0`/`priority` cases, `casez`, `casex`, `inside`,
patterns, nonintegral expressions and default-only cases remain loud.
Purity is checked on the bound source tree before constant conversion;
context widening cannot erase a call or increment into an admitted literal.
Any frontend error in a compilation containing a lowered case adds
`CaseStatement:invalid-compilation`; recovery cannot silently admit an
invalid program. The symbolic `sv-0.2` case path is unchanged.

### Fixed-size bitstream queries — 2026-10-10

The legacy/self-check extractor admits `$bits(expression)` and
`$bits(data_type)` when the bound argument is both fixed-size and a
bitstream type (IEEE 1800-2023 §§6.24.3, 20.6.2). It reads the type's
bitstream width, not the runtime-value fragment's integral width. Fixed
unpacked arrays and structures therefore work as query types even though
their runtime values remain outside this tier. Bound aliases and enums
are transparent to the query, and packed aggregates need no new value
constructor.

The argument is never evaluated or recursively converted: IEEE specifies
type inspection, not operand execution. An eligible query is a pure leaf for
ordinary-case admission, without admitting general calls or effects in
case subjects or labels. The result is a signed 32-bit integer, encoded
modulo `2^32`, independently of the queried type's width or signedness;
surrounding arithmetic and assignment conversions retain their existing
rules. The result compiles to the existing literal expression, so no
interpreter, process or scheduler rule changes.

Admission currently requires a syntactically pure bound argument:
calls other than nested admitted `$bits` queries, assignments, increments,
decrements, allocation and other unrecognized operand forms stay loud.
This is a tier restriction, not an IEEE evaluation rule. A focused
differential diagnostic observed an operand side effect for
`$bits(subject++)`, contrary to §20.6.2; the model does not emulate
that effect or count it as agreement. Pure query types,
operators and selections remain admitted without executing their operands.

Dynamic arrays, queues, associative arrays, string variables/types and
other dynamically sized arguments remain loud rather than reading live
storage. Fixed non-bitstream types, including `real` and unpacked unions,
remain loud too. Invalid interface-class queries are not admitted. Query
literals retain `fixed_bits_query: true` provenance through context
conversions; any frontend error in such a compilation adds
`$bits:invalid-compilation`. The symbolic `sv-0.2` query path is unchanged.

Six original fixtures in `harness/sv/bit_queries/` cover builtin types,
local aliases/enums, fixed unpacked arrays, packed aggregates, pure metadata
expressions and result contexts, with independent differential checks.
Fresh final extraction admits 60 previously partial simulation files
without losing a clean file: 1,577 clean, 20,180 partial and 30
include-skipped out of 21,787. The exact 3,148-key core grows from 192
to 196 clean files, with 2,948 partial and four include skips. Both
censuses report zero extraction errors; these are extractor completeness
measurements, not whole-corpus simulator agreement.

### Integral bit-vector queries — 2026-10-10

The legacy/self-check path now admits the five IEEE 1800-2023 §20.9
functions: `$countbits`, `$countones`, `$onehot`, `$onehot0` and `$isunknown`.
This addresses the largest computational system-call family in the fresh
sole-`CallExpression` inventory; delays and hierarchy remain separate
kernel and surface dependencies, not reasons to invent another scheduler.

Each operand is evaluated at its own bound integral width. `$countbits`
also evaluates its control expressions, uses each control's least
significant bit, and counts matching positions once even when controls
repeat. All four bit values are distinct: x and z can be counted
independently. `$countones` ignores x/z; the one-hot functions compare the
number of definite ones with one or at most one, respectively, and
`$isunknown` detects either x or z. Counts are signed 32-bit integers;
the three predicates return known one-bit results. Query results retain
the existing assignment and expression context conversions.

The new `BitQuery` envelope and self-check expression lower to the existing
`Logic`/`LVec` value authority. No process or scheduler rule changes.
Ordinary cases can use these pure expressions without admitting general
calls or effects. Runtime values outside the supported integral fragment,
including fixed unpacked bitstreams, remain loud; so do effectful operands,
bad arities and user functions whose escaped names resemble system queries.
An admitted query in an erroneous compilation retains a
`BitQuery:invalid-compilation` refusal rather than hiding frontend errors
through constant folding. The symbolic `sv-0.2` path is unchanged.

Four original fixtures in `harness/sv/bit_vector_queries/` pass independent
differential checks and cover four-state values, live controls and their
truncation/deduplication, integral types and widths, nested expressions,
result contexts and ordinary cases. The duplicate-control theorem in
`Examples/system-verilog/bit_vector_queries/` is symbolic over operand and
control values, with its expression pinned to the real extracted
`runtime_controls.sv` assignment and concrete non-vacuity checks.

Fresh extraction admits 75 formerly partial files and loses no clean
file: full **1,652 clean / 20,105 partial / 30 include skips**, out of
21,787; exact core **199 clean / 2,945 partial / four include skips**, out
of 3,148. Both report zero extraction errors and every shared core/full
classification agrees. These are extraction measurements, not a claim of
whole-corpus simulator agreement.

### Constant fixed-unpacked element cells — 2026-10-19

The legacy/self-check extractor now admits a narrow §10.2 memory-word shape:
one-dimensional fixed-unpacked arrays whose elements are integral scalars or
packed vectors, when each runtime element access has a constant in-range
index. It expands the declaration into vector-valued cells (`mem[0]`,
`mem[1]`, …), so existing `LVec` state and assignment semantics provide the
read/write behavior without inventing an aggregate store. Ascending and
descending constant ranges, 4-state initialization, 2-state zero
initialization, equality reads, and blocking writes are covered by the real
`unpacked_cells` fixture and its proof.

Dynamic or out-of-range indices, multidimensional and aggregate arrays,
whole-array assignment, and array-specific methods remain loud. This is a
self-check lowering only; symbolic `sv-0.2`, scheduler ownership and the M0
cycle loader are unchanged. On the fresh **22,033**-path census, clean
extraction rises **2,628 → 2,691** (63 gains, no losses), while the
`AssignmentExpression:target` refusal falls **4,473 → 4,314** files. These
are extractor measurements; only the authored fixture has a Lean execution
check and independent simulator startup on this host was unavailable.

### Whole-vector arbitrary packed ranges — 2026-10-19

Whole-vector declarations and operations now accept a single packed scalar
range regardless of its left/right direction (for example, `logic [0:7]`).
LVec values represent the vector's bits independently of the declared index
labels, so ordinary assignment, equality and rendering need no new storage.
Selected access on a noncanonical range remains loud until the evaluator
carries the declared bounds and maps an index explicitly. Multidimensional
packed arrays and nonintegral aggregates remain outside this rung. The
`packed_ranges` fixture checks the real envelope through the self-check runner.

The fresh **22,033**-path census adds **35 clean files** without losses
(**2,691 → 2,726**); `AssignmentExpression:target` falls to **4,224** files.
The new top refusal is `CallExpression` at **4,226**, so the next family is
priced from that queue rather than from the stale assignment count.

### Time-zero `$time` queries — 2026-10-19

The legacy/self-check extractor folds a zero-argument `$time` expression to a
64-bit zero literal carrying `time_zero` provenance. The self-check runner has
no elapsed time, so this is the IEEE time-zero result; delays and event waits
remain scheduler-owned and loud. Nonzero-argument or malformed calls remain
unsupported, as do `$realtime` and other time queries. The `time_zero` fixture
checks the real envelope through Lean's self-check runner.

The fresh **22,033**-path census adds **63 clean files** without losses
(**2,726 → 2,789**) and reduces `CallExpression` from **4,226 to 3,565**.
`AssignmentExpression:target` is again the top refusal at **4,224** files;
the next item must return to that heterogeneous class after this call rung.

### Constant bit selects on arbitrary packed ranges — 2026-10-19

Constant in-range bit selects on the admitted noncanonical packed ranges now
map their declared index label to the existing LVec offset. The normalized
index is recorded as a literal, so both selected reads and writes reuse the
ordinary self-check evaluator. Dynamic and out-of-range indices, indexed or
simple part selects, and multidimensional packed arrays remain loud until
their range geometry is represented directly. The `packed_range_select`
fixture checks an ascending `[0:7]` write/read pair through Lean.

The fresh **22,033**-path census adds **6 clean files** without losses
(**2,789 → 2,795**) and lowers `AssignmentExpression:target` by one file to
**4,223**. This is a narrow geometry rung; the remaining target wall is still
dominated by arrays, classes, hierarchy and nonintegral values.

### Positional fixed-unpacked initializers — 2026-10-19

Eligible one-dimensional fixed-unpacked integral arrays may now carry an
exact-length positional assignment pattern at declaration time. The
extractor converts each element once and installs it in the corresponding
vector cell, retaining ordinary 4-state and 2-state initialization. Keyed or
default patterns, wrong-length patterns, effectful elements and aggregate
element types remain loud. The `unpacked_init` fixture checks the initialized
cell through the real envelope and self-check runner.

The fresh **22,033**-path census adds **3 clean files** without losses
(**2,795 → 2,798**). This initializer rung does not reduce the target wall
itself; the remaining `AssignmentExpression:target` count is **4,223**.

### Direct packed-struct field windows — 2026-10-19

Direct fields of an untagged packed struct or packed union now reuse the
aggregate's vector storage: the extractor records each field's fixed bit
offset as a `SelectRead` or `SelectTarget` window. Whole packed aggregate
variables therefore retain the ordinary LVec width and four-state behavior.
Nested member chains, unpacked structs/unions, class and interface members,
tagged unions, and fields with nonintegral types remain loud. The
`packed_struct` fixture checks a direct field write/read through the real
self-check envelope.

The fresh **22,033**-path census adds **88 clean files** without losses
(**2,798 → 2,886**). `AssignmentExpression:target` falls **4,223 → 4,051**
and `MemberAccessExpression` falls **1,299 → 1,203**. The target family is
still led by unsupported array, class, hierarchy and string storage.

### Whole-array positional assignment patterns — 2026-10-19

An eligible one-dimensional fixed-unpacked integral array may now receive an
exact-length positional assignment pattern. The extractor lowers the
target-independent pure elements into per-cell blocking or nonblocking
assignments in declared index order, so the existing vector-cell state and
self-check evaluator provide the storage and update behavior. Keyed/default,
wrong-length, dynamic, aggregate and destination-aliasing patterns remain
loud. The `unpacked_assign` fixture checks the real envelope through Lean.

A paired run over the **22,029** paths available on this checkout adds four
clean files with no losses and lowers `AssignmentExpression:target` by 23
files (**4,049 → 4,026**). The committed 22,033-path census remains the
project snapshot; this local paired measurement is recorded separately because
the external corpus checkout has four fewer paths.

### Assignment-target repricing — 2026-10-19

On the paired checkout, **87** files remain blocked solely by
`AssignmentExpression:target`, covering **117** target instances. The shape
counts are 30 keyed/default or unpacked-array pattern targets in 29 files, 21
dynamic element targets in 17 files, 16 concatenated or streaming targets in
15 files, 18 whole aggregate/array targets in 13 files, 13 packed or unpacked
part-select targets in 9 files, 16 member targets in 7 files, and 3 constant
element/bit targets in 3 files; file counts overlap when a file has several
shapes.

This repricing does not admit another broad target shape. Dynamic and unpacked
aggregate targets need a runtime aggregate store, continuous concatenation and
part-select targets need the scheduler-facing continuous-assignment model, and
nested/unpacked/class/interface members remain outside the direct packed-struct
window tier. The next target item must first provide one of those prerequisites.

### Bounded dynamic fixed-array cells — 2026-10-19

Pure integral dynamic indices into an eligible one-dimensional fixed-unpacked
array now dispatch through a finite chain of case-equality conditions over its
expanded cells. Writes become mutually exclusive blocking or nonblocking
branches; reads become a `Ternary` chain with an all-x default. This preserves
x/z index no-op behavior and out-of-range reads without introducing an
aggregate runtime store. Associative, dynamic, queue, multidimensional and
effectful index forms remain loud. The `unpacked_dynamic` fixture checks the
real envelope through Lean.

On the paired **22,029** paths available on this checkout, the rung adds 17
clean files with no losses and lowers `AssignmentExpression:target` by 27
files (**4,026 → 3,999**). The committed 22,033-path census remains the
project snapshot; this local paired measurement is recorded separately because
the external corpus checkout has four fewer paths.

### Equal-length fixed-array copies — 2026-10-19

Whole assignment between equal-length one-dimensional fixed-unpacked integral
arrays now pairs source and destination cells in declaration order, reusing
the existing vector-cell state. Incompatible lengths or element widths,
conditional aggregate expressions and unsupported storage forms remain loud.
The `unpacked_copy` fixture checks the real envelope through Lean.

On the paired **22,029** paths available on this checkout, this rung adds
nine clean files with no losses and lowers `AssignmentExpression:target` by
21 files (**3,999 → 3,978**). The committed 22,033-path census remains the
project snapshot; this local paired measurement is recorded separately because
the external corpus checkout has four fewer paths.

### Conditional fixed-array assignments — 2026-10-19

Pure one-condition ternaries over equal-length fixed-unpacked integral arrays
now lower each destination cell to a `Ternary` value over the corresponding
source cells. An x condition preserves the per-bit merge; patterns, calls,
unequal shapes and unsupported aggregate storage remain loud. The
`unpacked_conditional` fixture checks the real envelope through Lean.

On the paired **22,029** paths available on this checkout, this rung adds
three clean files with no losses and lowers `AssignmentExpression:target` by
four files (**3,978 → 3,974**). The committed 22,033-path census remains the
project snapshot; this local paired measurement is recorded separately because
the external corpus checkout has four fewer paths.

### Constant fixed-array slice patterns — 2026-10-19

An exact-length positional assignment pattern on a simple in-range constant
slice of a one-dimensional fixed-unpacked integral array now lowers to one
blocking or nonblocking assignment per selected cell, in slice source order.
Dynamic or indexed bounds, out-of-range slices, keyed/default patterns and
effectful or mismatched patterns remain loud. The `unpacked_slice` fixture
checks the generated envelope through Lean and the self-check runner.

On the paired **22,029** paths available on this checkout, this rung adds one
clean file with no losses and lowers `AssignmentExpression:target` by two
files (**3,974 → 3,972**). The committed 22,033-path census remains the
project snapshot; this local paired measurement is recorded separately because
the external corpus checkout has four fewer paths.

### Structured and replicated fixed-array patterns — 2026-10-19

Elaborated keyed/default assignment patterns on eligible one-dimensional
fixed-unpacked integral arrays now lower their per-cell elements in declaration
order. Constant replicated patterns are admitted when their repetition count
equals the array length. Every element still must be a pure integral expression
that does not read the destination array, so wrong-length, dynamic, aggregate
and destination-aliasing forms remain loud. The `unpacked_patterns` fixture
checks both forms through Lean and the self-check runner.

The external `sv-tests-2` checkout was unavailable for this turn, so the
committed census snapshot is unchanged and this rung makes no fresh
whole-corpus coverage claim. The focused extractor and harness tests provide
the measured acceptance boundary; the next census rerun will price any newly
clean corpus files.

### Structured and replicated fixed-array initializers — 2026-10-19

Fixed-unpacked integral declarations now use the same elaborated structured
keyed/default cells and exact-length constant replication as assignment
statements. Each initializer element is converted once into its declaration
cell; wrong-length, effectful and aggregate initializers remain loud. The
`unpacked_init_patterns` fixture checks both forms through Lean and the
self-check runner.

The external `sv-tests-2` checkout was unavailable for this turn, so the
committed census snapshot is unchanged and this rung makes no fresh
whole-corpus coverage claim. The focused initializer tests establish the
admission boundary; the next census rerun will price any newly clean rows.

### Constant part selects on arbitrary packed ranges — 2026-10-19

In-range constant simple part selects on one-dimensional noncanonical packed
ranges now reuse the existing selected-window evaluator. The extractor maps
the right source label to its LVec offset and retains the selected width for
both reads and writes. Dynamic, out-of-range and indexed part-selects remain
loud. The `packed_range_part_select` fixture checks the normalized read/write
pair through Lean and the self-check runner.

The external `sv-tests-2` checkout was unavailable for this turn, so the
committed census snapshot is unchanged and this rung makes no fresh
whole-corpus coverage claim. The focused range tests establish the admission
boundary; the next census rerun will price any newly clean rows.

### Constant fixed-array slice copies — 2026-10-19

Equal-length simple constant slices of eligible one-dimensional fixed-unpacked
integral arrays now pair their expanded vector cells for copy assignments. A
whole array may appear on either side. Overlapping self-copies remain loud to
avoid exposing an earlier lowered write to a later source cell; dynamic,
indexed and out-of-range slices also remain loud. The `unpacked_slice_copy`
fixture checks the cellwise copy through Lean and the self-check runner.

The external `sv-tests-2` checkout was unavailable for this turn, so the
committed census snapshot is unchanged and this rung makes no fresh
whole-corpus coverage claim. Focused slice-copy tests establish the admission
boundary; the next census rerun will price any newly clean rows.

### Structured and replicated fixed-array slice patterns — 2026-10-19

Simple constant fixed-array slices now accept frontend-elaborated keyed/default
patterns and constant replicated patterns whose count equals the selected
slice length. Each selected cell receives the corresponding pure integral
value; dynamic, indexed, out-of-range and mismatched forms remain loud. The
`unpacked_slice_patterns` fixture checks both forms through Lean and the
self-check runner.

The external `sv-tests-2` checkout was unavailable for this turn, so the
committed census snapshot is unchanged and this rung makes no fresh
whole-corpus coverage claim. Focused slice-pattern tests establish the
admission boundary; the next census rerun will price any newly clean rows.

### Conditional fixed-array slice assignments — 2026-10-19

Equal-length simple constant slices on a fixed-unpacked destination and both
branches of a pure ternary now lower cellwise to the existing `Ternary` nodes.
Overlapping source/destination array names remain loud because the cell-expanded
state has no aggregate snapshot; dynamic, indexed and out-of-range slices also
remain loud. The `unpacked_slice_conditional` fixture checks the normalized
cellwise result through Lean and the self-check runner.

The external `sv-tests-2` checkout was unavailable for this turn, so the
committed census snapshot is unchanged and this rung makes no fresh
whole-corpus coverage claim. Focused conditional-slice tests establish the
admission boundary; the next census rerun will price any newly clean rows.

### Fixed-array equality and inequality — 2026-10-19

Equal-length whole fixed-unpacked arrays and simple constant slices now lower
their `==` or `!=` comparisons to pairwise cell comparisons joined by logical
`&&` for equality and `||` for inequality (corrected 2026-10-20), reusing the
existing four-state scalar operators. Unequal shapes and
unsupported aggregate types remain loud. The `unpacked_compare` fixture checks
whole-array and slice comparisons through Lean and the self-check runner.

The external `sv-tests-2` checkout was unavailable for this turn, so the
committed census snapshot is unchanged and this rung makes no fresh
whole-corpus coverage claim. Focused comparison tests establish the admission
boundary; the next census rerun will price any newly clean rows.

### Fixed-array case equality and inequality — 2026-10-19

Equal-length whole fixed-unpacked arrays and simple constant slices now lower
`===` and `!==` to pairwise cell case comparisons joined by logical `&&` for
equality and `||` for inequality (corrected 2026-10-20), so
four-state x/z identity follows the existing scalar case operators. Unequal
shapes and unsupported aggregate types remain loud. The `unpacked_compare`
fixture checks both ordinary and case comparisons through Lean and the
self-check runner.

The external `sv-tests-2` checkout was unavailable for this turn, so the
committed census snapshot is unchanged and this rung makes no fresh
whole-corpus coverage claim. Focused case-comparison tests establish the
admission boundary; the next census rerun will price any newly clean rows.

### Unpacked-array concatenation into fixed cells — 2026-10-19

Exact-length unpacked-array concatenations on eligible fixed-unpacked integral
destinations now flatten scalar and eligible whole-array/simple-slice operands
in source order and lower them to the existing cell assignments. Destination
aliases, dynamic or aggregate operands and mismatched lengths remain loud. The
`unpacked_concat` fixture checks the real envelope through Lean and the
self-check runner.

The authoritative `sv-tests-2` checkout is available at the coordinator's
read-only corpus path for this measurement. After validation, the census will
report **2,952 clean / 19,015 partial / 66 include skips** with zero extraction
errors, nine clean gains and no losses; `AssignmentExpression:target` falls
**3,939 → 3,929**. The committed machine-readable census remains the prior
snapshot because it is generated output; this paired result is recorded here.

### Unpacked assignment-pattern LHS — 2026-10-19

A positional unpacked assignment-pattern LHS such as `U3'{a, b, c} = source`
now lowers to scalar cell assignments when the RHS is an eligible fixed
unpacked integral array or simple constant slice. Source cells are sampled in
order and converted to each destination's width and state kind. Nested,
effectful, duplicate or source-aliasing targets, and aggregate or dynamic RHS
forms remain loud. The `unpacked_pattern_lhs` fixture checks the real envelope
through Lean and the self-check runner; focused extraction covers the
§10.9.11 row, without a new whole-corpus simulator-agreement claim.

### Right-streaming unpack targets — 2026-10-19

Simple right-streaming unpack targets with no slice size and direct integral
identifier leaves now reuse the existing packed `ConcatTarget` path. The RHS
is sampled once; a wider source contributes its leading target-width bits.
Left streaming, nested/effectful streams, unpacked aggregate leaves and
narrower sources remain loud. The `streaming_unpack` fixture checks
the real envelope through Lean and the self-check runner, without a new
simulator-agreement claim. The fresh **22,033**-path census reports **2,960
clean / 19,007 partial / 66 include skips** with zero extraction errors: seven
clean gains and no losses; `AssignmentExpression:target` falls **3,928 →
3,920**.

### Legacy streaming packed-member windows — 2026-10-20

The legacy right-streaming path now accepts a constant member chain through an
untagged packed struct or union as one fixed `SelectTarget` window. The
`streaming_aggregate_member` fixture splits one sampled four-bit source into a
two-bit member and scalar output, and nested packed-union alias leaves are
pinned by the focused extractor battery. Dynamic or effectful member indices,
nested streaming operators, left streaming and sized streams remain loud; the
existing flat vector state and packed-target executor are reused.

### Whole packed values in right-streaming targets — 2026-10-20

Whole untagged packed structs and unions, including typedefs, local values and
flattened fixed-array cells, now reuse the legacy `ConcatTarget` whole-vector
leaf. Field order and alternate union fields follow their existing packed
offsets. The `streaming_packed_value` fixture checks four-state field reads,
union aliasing and a wider source's leading bits; its two kernel theorems are
checked against the extracted statements. A completed simulator run agrees
with its full transcript and with the newly admitted §11.4.14 corpus row.

The wider-source check exposed a prior truncation error in both extraction
modes. Streaming unpack must take the leading target-width bits under
§11.4.14.3; the former packed resize kept the low bits instead. Both paths now
select the leading window before assigning it. The symbolic
`streaming_leading_bits` case matches all three simulator cycles in both
source and reverse process orders. Narrower sources, unpacked
aggregate values, dynamic/effectful leaves and overlapping targets remain loud.

A paired census on the same **22,035** source paths reports **2,979 → 2,980
clean**, **18,990 → 18,989 partial**, **66 include skips** and **zero
extraction errors**, with exactly one clean gain and no losses. The target
wall falls **3,942 → 3,941**; the regenerated machine-readable summary records
this snapshot. This is extraction coverage, not corpus-wide execution evidence.

### Packed right-streaming source expressions — 2026-10-20

Right-streaming sources now lower through their bound integral conversion to
an existing source-order concatenation. Optional slice sizes do not reorder
right streams (§11.4.14.2). When the destination is wider, an explicit trailing
zero part supplies the right padding required by §11.4.14.3, followed by the
destination's two-state conversion. The `streaming_pack` fixture checks x/z,
signed source bits, ignored slice sizes, source order and padding; a symbolic
kernel theorem proves its extracted padded assignment for arbitrary values.
The `streaming_pack_fixed` symbolic fixture covers continuous and procedural
sources in both process orders. Both authored fixtures match completed
simulator transcripts, and all 18 newly clean corpus files match on their full
observable output.

The paired **22,035**-path census gains **18 clean files** with no losses:
**2,980 → 2,998 clean**, **18,989 → 18,971 partial**, **66 include skips**,
zero errors. The streaming-conversion wall falls **55 → 36** files; one
additional partial file loses that wall while retaining an array declaration
wall. Left/nested streams, unpacked aggregate operands, `with` selectors,
effectful sources and destinations smaller than the stream remain loud.
Symbolic parameter/generate families remain loud until padding has symbolic
widths. No interpreter, storage or scheduler rule was added.

### Packed left-streaming source expressions — 2026-10-20

Left-streaming sources now lower to fixed packed selects and concatenation.
Under §11.4.14.2, chunks are taken from the right (default size one), emitted
low chunk first, and retain their internal bit order. The final short high
chunk stays short. Destination zero padding follows the complete reordered
stream. A slice at least as wide as the source preserves the original value.
The pure-source guard runs before lowering; duplicated selected reads cannot
hide a source effect. `streaming_left` checks x/z, one-bit reversal, oversized
slices, short chunks and wider destinations, with a symbolic kernel theorem
tied to the real extracted chunk expression. `streaming_left_fixed` exercises
both symbolic assignment paths and execution orders. The symbolic elaborator
now recognizes concatenations as flat vectors with one-bit elements, reusing
its existing slice evaluator. Both authored fixtures and all 20 newly clean
corpus files are checked against completed simulator transcripts.

The paired **22,035**-path census gains **20 clean files** with no losses:
**2,998 → 3,018 clean**, **18,971 → 18,951 partial**, **66 include skips**,
zero extraction errors. The streaming-conversion wall falls **36 → 16**
files. Nested/effectful streams, `with` selectors, unpacked aggregate operands,
smaller destinations and symbolic parameter/generate families remain loud.
This is a surface lowering through the existing value evaluator; no storage
or scheduler rule was added.

### Legacy continuous fixed-window targets — 2026-10-20

Continuous assignments in the legacy/self-check envelope now admit constant
packed bit/part selects, fixed concatenation leaves, and direct members of
untagged packed structs or unions as fixed `SelectTarget` windows. Static
overlapping windows are converted to a loud target refusal before they could
imply driver resolution; dynamic or effectful selectors, tagged aggregates,
dynamic fixed-array cells and unsupported nets remain loud. A
constant cell is an ordinary flat identifier; the vector executor is reused
and no net-resolution or scheduler rule is added.

### Legacy continuous nested packed-struct windows — 2026-10-20

Constant bit, simple part and indexed selections through nested untagged
packed-struct member chains on continuous assignments now flatten their fixed
declaration offsets into the same `SelectTarget` and `SelectRead` windows over
one vector.
The same composition applies to a constant selection through a flattened
fixed-array aggregate cell. Nested untagged packed unions use the same
flat-vector alias windows; dynamic or effectful selections, tagged aggregates
and unpacked storage remain loud. No aggregate store, driver-resolution rule
or scheduler is added.

### Legacy continuous packed-union alias windows — 2026-10-20

Direct members of an untagged packed union on continuous assignments now share
the same fixed-vector windows as struct fields, including constant bit, simple
part and canonical indexed selections. Alternate-member windows alias the same
base, so statically overlapping continuous drivers are rejected before they
could imply resolution. Nested untagged unions use the recursive fixed-window
path below; tagged unions, dynamic/effectful selections and unpacked storage
remain loud. No alias table, aggregate store or scheduler is introduced.

### Legacy continuous nested packed-union alias windows — 2026-10-20

Constant selections through nested untagged packed unions now accumulate the
fixed outer member offsets and flatten to the existing `SelectTarget` and
`SelectRead` windows. Alternate nested-union members therefore alias one flat
vector, and the static overlap guard rejects conflicting continuous drivers
before they could imply resolution. Dynamic/effectful selections, tagged
aggregates and unpacked storage remain loud; no alias table, aggregate store or
second scheduler is introduced.

### Legacy continuous fixed-array cell windows — 2026-10-20

The same legacy continuous-assignment window path now has a pinned boundary
for constant packed selections inside a flattened fixed-unpacked cell. Simple,
indexed and noncanonical in-range cells retain their cell identifier as the
window base and normalize declaration labels to the existing vector offset.
Static overlap on one cell is rejected before it could imply driver
resolution. Dynamic or effectful packed indices, out-of-range selections,
aggregate storage and dynamic array indices remain loud; no aggregate store,
net-resolution rule or second scheduler is introduced.

### Legacy continuous noncanonical indexed windows — 2026-10-20

Constant `+:` and `-:` selections on noncanonical packed ranges now reuse the
legacy fixed-window path. Direct vectors, nested untagged packed-struct
members, and flattened fixed-array cells normalize the indexed base label to
the existing LVec offset while retaining the indexed direction. Dynamic or
effectful bases, out-of-range windows, aggregate storage and unsupported
net-resolution forms remain loud; no declaration-range table, aggregate store,
or scheduler is added.

### Legacy continuous right-streaming cell windows — 2026-10-20

Continuous assignments with a simple right-streaming target now reuse the
legacy `ConcatTarget` path when every leaf is a direct integral identifier,
a constant packed window, a fixed-array cell, or a fixed-array cell window.
The RHS is sampled once and the existing MSB-to-LSB split handles excess
source bits. Left streaming, explicit slice sizes, nested or effectful
streams, dynamic array cells, aggregate leaves and overlapping windows remain
loud; this adds no aggregate storage, driver-resolution rule or scheduler.

### Symbolic streaming targets over fixed cells — 2026-10-20

The symbolic `sv-0.2` procedural surface now applies the same right-streaming
`ConcatTarget` lowering to constant packed windows and constant cells of a
one-dimensional fixed-unpacked integral array. `fixed_array_stream_target`
checks one sampled five-bit RHS split into `arr[0]` and a scalar output, then
reads the cell through the existing comb-settle path. Dynamic or effectful
array indices, dynamic packed bounds, left/sized/nested streams and aggregate
leaves remain loud; no aggregate store or scheduler behavior is introduced.
This is a semantic-tier fixture and does not claim a legacy corpus gain or
simulator agreement on this host.

### Symbolic continuous streaming targets over fixed cells — 2026-10-20

Continuous right-streaming assignments now use the same symbolic
`ConcatTarget` lowering as procedural streams when every leaf is a constant
packed window or a constant cell of a one-dimensional fixed-unpacked integral
array. `fixed_array_stream_continuous` checks one sampled five-bit source split
into `arr[0]` and a scalar output, with a second continuous readback through
the existing comb-settle path. Dynamic/effectful leaves, left/sized/nested
streams, aggregate storage and overlapping windows remain loud; no second
scheduler is introduced and no simulator-agreement claim is made.

### Symbolic continuous right-streaming packed-union leaves — 2026-10-20

Continuous right-streaming assignments now admit constant leaves through
nested untagged packed structs and unions when those leaves flatten to disjoint
fixed `PartSel` windows over one vector. Alternate union fields therefore keep
their aliasing visible: overlap within one streaming target, overlap with an
earlier continuous driver, and dynamic or effectful selections remain loud.
No aggregate storage, net-resolution behavior or scheduler is added, and this
is a semantic fixture result without a simulator-agreement claim.

### Nested packed-struct field windows — 2026-10-19

Member reads and writes through untagged nested packed structs now flatten
their fixed declaration offsets into one vector window over the outer
aggregate. Nested unions, unpacked members, classes, interfaces and tagged
aggregates remain loud. The `packed_struct_nested` fixture checks the real
envelope through Lean and the self-check runner, without a new
simulator-agreement claim. The fresh **22,033**-path census reports **2,975
clean / 18,992 partial / 66 include skips** with zero extraction errors: 15
clean gains and no losses; `AssignmentExpression:target` falls **3,920 →
3,909**.

### Typed assignment-pattern operands in unpacked concatenations — 2026-10-19

Unpacked-array concatenations now also flatten typed simple assignment-pattern
operands whose fixed-array elements are pure integral values at the destination
width. Replicated, nested or mismatched pattern operands remain loud. The
focused §10.10.1 rows extract cleanly. The fresh **22,033**-path census
reports **2,979 clean / 18,988 partial / 66 include skips** with zero
extraction errors: four clean gains and no losses; `AssignmentExpression:target`
falls **3,909 → 3,904**. This is not a simulator-agreement claim beyond the
fixture.

### Nested replicated assignment patterns — 2026-10-19

Fixed-array assignment-pattern replication now repeats an inner positional
element list when the constant repetition count times that list length equals
the destination length. Wrong-length, effectful and aggregate forms remain
loud. The §5.11 nested-replication row and a focused fixture pass through the
self-check runner; the fresh census below records the paired result.

The fresh **22,033**-path census reports **2,980 clean / 18,987 partial / 66
include skips** with zero extraction errors: one clean gain and no losses;
`AssignmentExpression:target` falls **3,904 → 3,902**. This is not a
simulator-agreement claim beyond the fixture.

### Packed blocking assignment targets — 2026-10-11

The next family addresses the identifier-only destination boundary, not a
new scheduler. The selected-write foundation now preserves bit, simple
part and indexed-up/down geometry, live signed indices, x/z index no-ops,
four-state data and per-destination two-state conversion. It reuses
`selectedIndex` and the existing `LVec.insertAt`/`extract` value authority.
The resumable stepper delegates the new leaf to the same executor.

Concatenated and nested concatenated blocking destinations now compile to
ordered packed leaves, retaining each leaf's width, live index and
two-state conversion. The RHS is captured once; each destination's index
is evaluated against the frame at that destination's write. An explicit
`AssignmentOrder` parameter selects a permutation of leaves; invalid
permutations refuse rather than skip or duplicate a destination. The
named default is `rightToLeftAssignmentOrder`, matching the observed
licensed reference, not a claim that IEEE mandates that order. The
statement, block and initial-process drivers thread this policy; the
existing resumable stepper instantiates the named default.

`harness/sv/packed_assignment_targets/runtime_updates.sv` is an actual
licensed self-check fixture. Its unknown-index store is pinned to the
extracted statement in `Examples/system-verilog/packed_assignment_targets/`,
with a value-symbolic state-preservation theorem. Focused builds and the
ordinary simulator comparison set pass; this is not a full repository
qualification.

`concat_updates.sv` is a second licensed fixture covering nested/mixed
leaves, per-leaf conversion, RHS snapshots, overlapping aliases and an
index that observes an earlier destination write. Its actual extracted
alias statement is pinned to a value-symbolic theorem under the named
reference order, with a separate invalid-oracle refusal theorem. The
focused build recompiles the stepper's subsumption proof unchanged;
51 byte-bound licensed comparisons and 58 extractor tests pass.

### Selected nonblocking packed targets — 2026-10-11

The legacy/self-check surface now admits one selected `<=` destination
(`SelectTarget`) without changing the scheduler. The RHS and index are
evaluated against the active state; an unknown index enqueues no window.
For a known index, the self-check queue stores a full-value snapshot formed
from the last pending snapshot for that signal, so disjoint selected writes
merge and overlapping writes retain issue order. Whole-value NBAs keep the
existing queue representation, and concatenated NBAs are admitted through
the same pending-snapshot queue path.

`harness/sv/packed_assignment_targets/nba_updates.sv` is the concrete
pre-commit visibility fixture. Its extracted statements are pinned in
`Examples/system-verilog/packed_assignment_targets/nba_updates.sv.json`,
and `selected_nba_snapshots` proves two live index changes produce the
ordered `0010`, then `1010` pending snapshots while the active frame stays
at zero. The theorem uses only the existing value and queue primitives.

The qualification probes exposed a disagreement on partly out-of-range
part destinations: one available simulator leaves them unchanged, while
the IEEE 1800-2023 §11.5.1 per-bit rule retains the in-range writes. The
staged value helper therefore follows the standard rule through the
existing value primitive; no simulator-specific path or rewritten
expectation is used. The diagnostic remains recorded as a known oracle
disagreement, outside the acceptance fixture. The selected family keeps
one full-value queue window per affected signal; the concatenated family
below uses the same snapshot rule rather than a silent whole-variable
fallback.

Fresh extraction is **1,680 clean / 20,077 partial / 30 include skips**
over the full 21,787 files, and **209 clean / 2,935 partial / four include
skips** over the exact 3,148-file core. There are zero extraction errors,
zero lost clean files and no shared-record discrepancy. These gains
(seventeen full, nine core since the selected-write foundation) measure extraction, not agreement on the disputed
runtime cases.

### Concatenated nonblocking packed targets — 2026-10-11

Concatenated `<=` destinations now lower to the legacy/self-check
`packedNbaAssign` form. Nested concatenations are flattened to the same
width-bearing `PackedTarget` leaves used by blocking assignments, while
the envelope retains the source nesting. The RHS is evaluated once and
each destination index is evaluated against the active state; an unknown
index contributes no queue entry. Each known leaf appends a full-value
snapshot, based on the latest pending snapshot for that signal, so aliasing
and disjoint selected leaves preserve the named right-to-left issue order.

`harness/sv/packed_assignment_targets/nba_concat_updates.sv` checks that
whole, nested and overlapping concatenated writes remain invisible before
the NBA commit. Its generated envelope is pinned in
`Examples/system-verilog/packed_assignment_targets/nba_concat_updates.sv.json`,
and `concat_nba_snapshots` proves the whole-value queue order
`second := 0101`, then `first := 1010`, while the active frame remains at
zero. Invalid destination permutations remain loud.

### Scalar compound assignments — 2026-10-11

This historical scalar boundary is extended by
[selected compound assignments](sv-compound-assignments.md), including the
complete bound conversion tree, as of 2026-10-20.

The legacy/self-check surface now lowers whole-signal compound assignments
on plain scalar identifiers to its existing blocking-assignment and
binary-expression nodes. The admitted
operators are `+=`, `-=`, `&=`, `|=`, and `^=`; the left operand is read once
through the ordinary identifier path, and the elaborated result width is
checked against both operands before lowering. This reuses the established
four-state arithmetic/bitwise value rules and two-state destination
conversion rather than adding a second compound-assignment evaluator.

Selected and concatenated destinations, unsupported compound operators,
timed assignments and elaborated width mismatches remain loud. The actual
`harness/sv/compound_assignments/updates.sv` fixture exercises the complete
five-operator sequence against the licensed simulator and the generated
envelope is pinned in `Examples/system-verilog/compound_assignments/`;
`compound_updates` proves the complete update sequence through the shared
self-check executor. The extractor regression suite covers the admitted
lowering and the principal refusal cases.
Symbolic compound assignments keep their previous loud boundary; this item
does not extend parameterized compound sizing.

Fresh extraction over the current 21,843-file corpus yields **1,662 clean /
20,115 partial / 66 include skips**, with zero extraction errors. All seven
classification changes are partial-to-clean; no previously clean file
regresses. Each newly clean row also prints `PASS` in both the model and
an independent external simulator. This is a seven-row runtime check, not
whole-corpus runtime agreement.

### Integral signing functions — 2026-10-11

The legacy/self-check path now admits the IEEE 1800-2023 §11.7.1 / §20.5
functions `$signed` and `$unsigned`. They preserve an admitted integral
operand's bits, width and two-state/four-state classification, replacing
only its result signedness. The existing expression is retained: no new
value operator, evaluator or scheduler rule is introduced. Consumers use
the frontend's elaborated types to select signed comparisons, decimal
output and sign or zero extension. The argument remains self-determined;
an outer assignment cannot widen it before the signing operation. A
mixed-sign arithmetic context can still demand zero extension, and a
concatenation remains unsigned.

Selected operands, nested signing functions, integral aliases and enums
reuse their established lowering. Pure calls participate in ordinary cases,
selected assignments and `$bits` queries without admitting effectful
operands. Invalid signatures, unmodelled operand expressions and erroneous
compilations stay loud; conversion folding cannot hide an admitted call's
diagnostic provenance. Symbolic `sv-0.2` calls keep their existing `Cast`
representation; no symbolic sizing extension is claimed.

Four original fixtures in `harness/sv/signing_calls/` are confirmed against
an independent external simulator and Icarus, covering assignment versus
mixed-sign contexts, four-state sign extension and two-state destination
squashing, reinterpretation and output, selected values, nested calls,
aliases, enums and predefined integral types. The generated real
`assignment_contexts.sv` envelope is pinned to `signingBody` in
`Examples/system-verilog/signing_calls/`; `signing_assignment_contexts`
proves the four assignment results for an arbitrary four-state operand,
including same-width bit preservation and the distinct widening rules.

On the same 21,843 corpus files, extraction moves **1,662 → 1,692 clean**,
with **20,085 partial / 66 include skips**, zero extraction/internal errors
and no clean-to-partial regressions. All 30 newly clean rows agree in
stdout and status with an independent simulator; this separate 30-row
runtime check does not claim whole-corpus runtime agreement.

### Four-state packed selected reads — 2026-10-09

The legacy/self-check surface admits bit, constant part and indexed
part reads (`[index]`, `[msb:lsb]`, `[base +: width]`, `[base -: width]`)
from four-state predefined integers and descending zero-based packed
scalar vectors (clause 11.5.1). Selected results are unsigned; slang's
bound conversions preserve that rule in enclosing contexts. Integral
indices retain their own signedness, with negative and unknown indices
handled at runtime. Indexed-minus lower bounds use integer subtraction,
not saturating natural subtraction. Each negative or out-of-bounds bit
reads `x`, while in-range bits preserve `0`/`1`/`x`/`z`; partial overlap
therefore preserves the in-range portion rather than becoming all-x.

The new `SelectRead` envelope node and self-check expression add no
process rule. They use the existing four-state bit-vector value inventory
and shared completed-step/executor correspondence. Original fixtures in
`harness/sv/selected_reads/` cover dynamic indices, partial overlap,
signedness, unknowns and both indexed directions.

Two-state selected sources were initially kept loud; the type-directed
packed selected-read extension below now admits their zero-filled results.
Scalar sources, unsupported declared ranges, multidimensional/unpacked
elements and selected writes also remain outside this admission.
The symbolic/Design2 selected-read path and the M0 loader are unchanged.
An envelope using this new node remains loud if the frontend reports
any compilation error, including a recovered malformed declaration whose
bound selected expression itself does not carry an invalid flag.

### Conformance validation status — 2026-10-09

The six cast, six typedef and eight selected-read fixtures pass independent
differential checks, including predefined integer/time sources and runtime
index expressions. This confirms these fixtures, not arbitrary source
shapes or nets. Expectations come from IEEE semantics; a simulator's exit
status alone is not acceptance of a self-checking fixture.

IEEE 1800-2023 11.5.1, printed page 296, requires X at the individual
out-of-range positions of a partially overlapping read. Note 2 on page 297
permits a compile-time error for an out-of-range index; it does not specify
an alternative whole-result-X value for accepted execution. The interpreter
and distinguishing fixture expectations retain the per-bit rule. Separate
diagnostics confirm exact `xx10` results for
ordinary, constant-indexed and runtime-indexed partial reads of known and
mixed-x/z sources, rather than checking only the out-of-range positions.
No theorem is weakened and no simulator-specific semantic path is introduced
to disguise a disagreement. This selected-read family is confirmed against
the IEEE per-bit rule; publication
still requires the ordinary build and CI gates.

---

## 0 THE CORRECTION THIS CHARTER OPENS WITH

The C tier was chartered onto a blank page: `LeanModels/C/` did not
exist, and the charter's job was to decide whether it should. **The SV
lane is not that, and a charter that pretended otherwise would be
wrong on line one.**

Measured today, on this clone, at `426fdb7`:

| | files | lines |
| --- | ---: | ---: |
| `LeanModels/Sv/` | 14 | **8 166** |
| `extractors/sv/` | 3 | **3 583** |
| `Examples/system-verilog/` | 18 designs + envelopes | — |
| `harness/sv/` | 8 | — |

`find LeanModels/<tier> -name '*.lean'`, summed. That makes SV the
**third-largest tier in the repository**, behind Python (32 331) and
Spice (23 366) and ahead of Circuit (4 309), Rv (2 041), C (934) and
VerilogA (606). It carries **86 `theorem`/`lemma`/`example`
declarations, zero `sorry`, zero `native_decide`** (`grep -rc` over
`LeanModels/Sv/*.lean`).

So this is not a founding in the sense of *starting*. It is a founding
in the sense the C charter meant when it found M0 already done and the
record not knowing: **the SV tier was built to a real milestone, then
went dormant, and the charter's first duty is to re-measure it and
correct the record.**

**The dormancy, dated.** The last commit touching `LeanModels/Sv`,
`extractors/sv` or `Examples/system-verilog` is `db9bb3e` *"CV32E40P
phase 2: symbolic sv-0.2 ingestion + semantic tier, dual-sim
validated"*, **2026-07-31**. `git rev-list --count db9bb3e..HEAD` =
**318**. The lane has been untouched for three weeks and 318 commits of
sibling traffic.

**What that dormancy did NOT break — every claim below is a run made
today, not a citation.**

1. **The differential harness is GREEN.** `python3 harness/sv/diff_test.py --sim iverilog`
   → **10 cases, 10 PASS, `overall: PASS`** against Icarus Verilog
   12.0. Nine matched `sigma_src`; `race_blk_one_edge` matched
   `sigma_rev` — i.e. the schedule oracle is not decoration, the racy
   example really does need the other schedule and the harness really
   does try it.

2. **The extractor still round-trips BYTE-IDENTICALLY — 18 of 18.**
   Re-running `extractors/sv/extract.py` over every pinned source in
   `Examples/system-verilog/` and diffing against the committed
   envelopes: **18 identical, 0 differing, 0 errors.** Six are schema
   `sv-0.1` (single-file), twelve are `sv-0.2` (symbolic `--top`).

   **This paragraph first published "17 of 18", and that was wrong
   twice over** — wrong in the count and wrong in the cause. The
   holdout, `cv32e40p_register_file_ff`, was blamed on a missing
   `cv32e40p_pkg.sv` from the un-vendored OpenHW checkout. In fact the
   file `cv32e40p_register_file_ff.sv` declares module
   `cv32e40p_register_file` — filename and module name differ, as they
   do across all three of OpenHW's register-file variants — so a
   `--top` derived from the *filename* could not resolve it. Read from
   the envelope's own `top` field it regenerates byte-identically **and
   needs no external checkout at all**. A plausible, unverified
   diagnosis survived a whole publication; `harness/sv_round_trip.py`
   now runs this check so the next one cannot.

3. **The tier still builds.** `lake build` reached **3 690 of 3 693
   jobs with ZERO compilation errors**, and **all 14 `LeanModels.Sv.*`
   modules built**. Stated exactly, because the run did not exit 0: two
   targets — `Examples.python.sunfish.bound_depth` and
   `…pins_clock`, both in the *Python* tier — died with `Lean exited
   with code 143`. **143 = 128 + 15 = SIGTERM: they were KILLED, not
   failed**, under the machine contention that prompted the
   repository-wide build lock the same afternoon. No SV target failed
   and no diagnostic was emitted by any target. The honest claim is
   therefore *"the SV tier builds clean; the run was interrupted
   elsewhere"* — not *"the build is green."*

**A methodological note that belongs in the charter because it twice
became a false finding.** The first round-trip run reported *12
differing*. That was the instrument, not the tree: the `sem2` envelopes
are `sv-0.2`, which requires `--top <module>`, and the loop had invoked
single-file mode. Re-run with the mode each envelope declares in its own
`schema_version` field, the differences vanished entirely. **An envelope
compared against the wrong extraction mode is a silent wrong answer of
exactly the C charter's kind**, and the rule it yields is now written
down: *read the mode out of the artefact, never assume it.*

The rule has **three** edges, and each was found by tripping over it:
the **schema** (`sv-0.1` vs `sv-0.2`), the **top module** (from the
envelope's `top`, never the filename — item 2 above), and the **source
path spelling**, because the recorded path is *part of the envelope*:
regenerating with absolute paths where the envelope recorded
repo-relative ones made all 18 differ, by exactly the string-length
delta. The gate now mirrors the recorded layout in a scratch directory
and runs there.

---

## 1 THE CENSUS — and the four defects it found

### 1.1 The frontend is `pyslang`, and it is NOT installed — **CLOSED**

`extractors/sv/extract.py` requires **python3.12 + pyslang 11.x** — the
Python bindings to **slang**, an MIT-licensed SystemVerilog frontend.
This settles the "which frontend can emit a usable AST" question the
charter was asked to census: **the lane chose one three weeks ago,
wrote 2 495 lines against it, and validated the result on two
simulators.** Verilator was not the answer and re-litigating it would
be re-work.

But measured today:

```
$ python3.12 -c "import pyslang"
ModuleNotFoundError: No module named 'pyslang'
```

**The lane's frontend is absent from this host.** Priced: a clean
`python3.12 -m venv` + `pip install pyslang` yields **pyslang 11.0.0**
— inside the extractor's declared 11.x range — in well under a minute,
no build, no system dependency. Every extractor claim in §0 was made
through that venv. So the gap is *unpinned*, not *unavailable*, and the
fix is a recorded dependency rather than an engineering effort.

**Why slang and not Verilator, recorded so it is not re-asked.** The
envelope needs a *source-level* AST with elaborated widths. Verilator's
`--json-only` emits its own post-elaboration IR after aggressive
inlining and generate-unrolling; slang's compilation exposes the
elaborated symbol table *beside* the syntax tree, which is what lets
the envelope carry `sv-0.1`'s resolved widths **and** `sv-0.2`'s
symbolic parameter binders. Verilator is also not plain-permissive
(LGPL-3/Artistic dual), where slang is MIT.

### 1.2 The corpus census cites an artefact that is NOT in the tree — **CLOSED**

`docs/sv-corpus-coverage.md` states its machine-readable results live
at `harness/sv/conformance/census.json`. Measured:

```
$ git ls-files harness/sv/conformance/
harness/sv/conformance/runner.lean
harness/sv/conformance/unlockable.txt
```

**`census.json` is not tracked and not present** — and the reason is
worse than an oversight: `.gitignore:5` lists
`harness/sv/conformance/census.json`, so the document cites an artefact
its own repository is configured to exclude. It was not forgotten; it
was **excluded by rule**, which looks deliberate and so invites nobody
to fix it.

**CLOSED.** The per-file records are 11.9 MB across 21 186 files, far
outside this repository's census range (6 KB - 773 KB in `docs/`), so
they stay regenerable-but-uncommitted while the half every claim
actually cites — provenance + summary, 20 KB, sorted — lands as
`docs/sv-construct-census.json`, with a `--compare` mode that exits
non-zero on drift. The document's
headline numbers — 21 336 files walked, the construct-frequency table
that it calls *"THE IMPLEMENTATION PRIORITY QUEUE"*, the per-chapter
coverage — are therefore **unreproducible from this repository**: the
aggregates survive only as prose in the memo that cites the missing
file. The sibling `unlockable.txt` (11 lines) did land, which is how
§1.4 below could be measured at all.

### 1.3 The census instrument points at a path that does not exist — **CLOSED**

The reproduce-block in `docs/sv-corpus-coverage.md` invoked `census.py`
with **no `--corpus` flag**. An obsolete absolute, host-local default
made that command unusable on other machines.

The instrument itself is *fine* — pointed at a corpus with `--corpus`
it runs, and a 40-file smoke completed in **2.0 s**. The defect is
purely the hard-coded default, and it is the SV analogue of exactly
what `--compare` was invented for in the C tier: **a corpus that lives
outside the repository, with no mechanical staleness check.**

**CLOSED.** The hard-coded path is replaced by a registry resolved by
`--corpus-name`, which tries candidate locations in order and
**REFUSES** with every path it tried when none exists (exit 2). Both
corpora are registered, so ruling §6.1's anchor is a flag rather than a
project. And the missing staleness check now exists: `--compare` reports
every drifting key against the committed summary. Verified — a
perturbed artefact is caught and exits 1; an unperturbed one reports
`compare: IDENTICAL (21186 files, corpus sv-tests-2)`; two consecutive
runs are byte-identical, once `elapsed_seconds` was removed from the
artefact for being a fact about the afternoon rather than the corpus.

### 1.4 THE HEADLINE: the censused corpus is NOT the public one

This is the finding that most changes what the owner is deciding.

`docs/sv-corpus-coverage.md` censuses a corpus it calls **sv-tests-2**.
The public `sv-tests` corpus is a separate checkout of the
public **chipsalliance/sv-tests**. The charter assumed, as any reader
would, that one was a checkout of the other. **They are disjoint.**

The decisive test — the 11 filenames `unlockable.txt` names, looked up
in the public suite:

```
present=0  missing=11
```

**Not one of them exists upstream.** They are not renamed; the public
suite has no `11.4.4--unsigned-comparison.sv`, no
`6.9.1--vector-unsigned-wrap-modulo-v3.sv`. The corpora are different
bodies of work.

Located and censused, read-only:

| | public `sv-tests` | `sv-tests-2` |
| --- | --- | --- |
| location | caller-supplied checkout | caller-supplied corpus directory |
| origin | `chipsalliance/sv-tests` | independently supplied test corpus |
| `.sv` files | **1 028** tracked | **21 631** (21 186 under `chapter-*`) |
| chapter dirs | 20, clauses 5–26 | **38, clauses 3–40** |
| licence | **ISC, uniform, per-file SPDX** | **none — no LICENSE file** |
| redistributable | yes, with attribution | **no** |

The extended corpus is organized by IEEE clause, covering the full SV
surface plus the VPI clauses.

**Three consequences, and the third is a hard blocker.**

1. **It is 21× the size and spans nearly twice the clause range.** It
   reaches clauses 27–40 — generate constructs, gate-level modelling,
   UDPs, specify blocks, timing checks, SDF, configurations, protected
   envelopes, DPI, and the whole VPI/assertion/coverage API surface —
   that the public suite does not test at all. As a *measuring
   instrument* it is far and away the better one.

2. **Its inputs must be independently accessible.** A public conformance
   claim needs a corpus readers can obtain and run. Counts from an
   unavailable external corpus cannot establish public reproducibility.

3. **It embeds the IEEE standard itself.**
   `tests/chapter-36/ieee-1800-2023.pdf`, 9 448 927 bytes. That is
   copyrighted IEEE text. The family law is *no ISO/IEEE text
   vendored, cite-and-paraphrase only*; this charter reports the file's
   existence and size and **has not opened it**. Any future rule that
   vendors or mirrors `sv-tests-2` wholesale would drag that PDF along,
   and must not.

Per-file licensing inside `sv-tests-2` is the **c-testsuite trap in its
purest form** — not a *conflicting* licence, but *no licence at all*:
in `tests/chapter-11`, **3 of 1 005 files carry an SPDX tag.**

### 1.5 The public suite, censused per-file — and its own trap

Because §1.4 makes the public suite the *vendorable* candidate, it was
censused to the standard the family law demands.

**Provenance.** `chipsalliance/sv-tests` at
`4f24807559e90dd26cb887517e2fedae160f672f`, 2026-01-15, exactly at
`origin/master`. `tests/` is unmodified; the working tree is dirty only
in `tools/runners/Verilator.py` and untracked build outputs. 33
submodules declared, **32 uninitialised**.

**Structure — and it is already clause-mirrored.** 1 028 `.sv` tests
organised *by IEEE 1800 chapter*: `chapter-18` 134, `chapter-7` 103,
`chapter-11` 88, `chapter-6` 84, `chapter-22` 75, `chapter-8` 53,
`chapter-16` 53, `chapter-5` 50, and a 185-file `generic/` bucket.
Metadata is a `:key: value` header block; **all 1 028 carry `:name:`,
`:description:` and `:tags:`.**

**1 381 tag occurrences over 326 distinct tags** — and the tags *are
clause numbers* (`5.6.4`, `8.3`, `11.5.1`, `22.5.1`). `conf/lrm.conf`
is a **482-entry clause dictionary** (457 numeric LRM clauses + 25
suite tags), of which **324 are exercised and 158 have zero coverage**.

**This is the charter's happiest finding: the organising principle the
SV tier needs is already agreed by the corpus.** The C tier had to
*invent* a mapping from its census to the standard's structure. Here
the corpus is indexed by clause number natively, `lrm.conf` is a
ready-made clause dictionary, and a coverage claim can be stated
per-clause without building any of that scaffolding. The densest holes
are named: **clause 6 (48/92 covered), clause 11 (25/54)**, clause 18
(39/55), clause 9 (23/33) — and clauses 6 and 11 are precisely the
two the M0 tier is closest to owning.

**Negative tests — a refusal corpus, pre-labelled.** **80 of 1 028
(7.8%)** carry `:should_fail_because:` with free-text LRM prose
("switch variable not declared"; "it is illegal to do bit select on
real data type"). The runner defaults `should_fail` to true exactly
when that reason is non-empty, so **every negative test carries a
human-readable rationale**. That is the raw material for a refusal
taxonomy, with the honest caveat that the strings are **not a
controlled vocabulary** and would need clustering.

**LICENCE — the verdict, per-file.** Top-level is **ISC** (SymbiFlow
Authors). Across `tests/`: **1 029 SPDX occurrences, every one `ISC`,
zero other licences**; 1 028 of 1 030 files tagged; the two untagged
are `tests/README.md` and a two-line `.svh` include. A contamination
scan for *"all rights reserved" / Accellera / proprietary /
non-commercial / GPL / Apache / BSD / Solderpad / confidential* across
`tests/` returns **0 hits**. Single copyright holder, single licence,
no exceptions.

**But the trap is real, and it is one directory away.** The suite the
project's dashboard actually reports on is *generated*:
`make generate-tests` synthesises `tests/generated/` (gitignored) whose
`:files:` keys point straight into `third_party/`. Licences reachable
that way include **GPL-2.0** (`ivtest`, from Icarus — verified against
`~/repos/iverilog/ivtest/COPYING`), Solderpad 0.51, BSD-3, MIT.
`third_party/cores/black-parrot` is 2 504 files with **zero** SPDX
tags.

> **Vendoring rule, stated for the family: `tests/**` only, never
> `third_party/**`, never `tests/generated/**`.** Under that rule the
> public suite is ISC-clean and attributable. Outside it, the tree
> reaches GPL-2.0 in one hop.

### 1.6 The re-census: the M0 extractor against the PUBLIC suite

Because §1.4 makes the public suite the only vendorable anchor, the
committed instrument was pointed at it — the first time the SV
extractor has been measured on the corpus it might have to live on.

`python extractors/sv/census.py --corpus ~/repos/sv-tests/tests --jobs 8`

The instrument walks `tests/chapter-*` only, so it sees **717** of the
1 028 tests (the 185-file `generic/` bucket, `testbenches/` and
`uvm/` sit outside any chapter and are out of its scope by
construction).

**The run does not complete — and finding out why is the most
actionable result in this charter.**

Bisected on `--limit` (each run `nice -n 19`, 4 jobs):

| limit | result |
| ---: | --- |
| 100 | completes, **1.6 s** |
| 200 | completes, **1.5 s** |
| 400 | completes, **1.5 s** |
| **500** | **never completes** (killed at 120 s) |
| 600, 717 | never completes (killed at 120 s, and at 600 s) |

At `--jobs 1` it also never completes, and the process sits at **0.0%
CPU in state `S`** — it is not working slowly, it is *stopped*.

**The cause, isolated to one file.** Reproducing the instrument's own
walk order (`sorted(os.listdir)` over `chapter-*`, one level deep,
717 files) and running the extractor on each of files 400-510
individually, exactly one is fatal:

```
rc=133   chapter-22/22.9--unconnected_drive-invalid-2.sv
```

**133 = 128 + 5 = SIGTRAP.** Re-run alone, redirected: `TRUE_RC=133`
and **zero bytes of output**. The whole file is two directives:

```
`unconnected_drive pull2
`nounconnected_drive
```

— a *negative* conformance test (`:should_fail_because: The directive
`unconnected_drive takes one of two arguments - pull1 or pull0`).
**pyslang 11.0.0 hard-crashes the interpreter on it, with no
diagnostic**, and `census.py`'s `multiprocessing.Pool` then waits
forever for a result from a worker that no longer exists.

**Two defects, and both are "never hide errors" violations.**

1. **The frontend dies on valid input to the tool** — a two-line source
   file that a conformance suite is *supposed* to reject gracefully.
   Upstream-reportable; the lane cannot fix it, only contain it.
2. **The instrument turns that crash into a HANG**, which is strictly
   worse than a crash: a hang has no exit code, no message, and no
   failing file name. A worker death must be reported as a per-file
   `error`, never absorbed. The existing 90-second per-file
   `signal.alarm` cannot help, because the process carrying the alarm
   is the one that dies.

**This CORRECTS what this charter would otherwise have concluded.**
The draft of this section read *"the extractor runs on the public suite
unmodified, so switching the anchor corpus is a licensing decision, not
an engineering one."* **That is false, and only running it showed so.**
Switching corpora costs at least: a crash-containment layer in the
census (per-file subprocess isolation, so a SIGTRAP becomes a recorded
`error` row), and an upstream bug report. It is a small cost — but it
is not zero, and the owner should price decision §8.1 knowing it.

**What the partial run does establish**, on the first 400 files
(chapters 10-21, complete): **294 partial, 13 clean, 33
`skip_include`** at limit 400. The tier's M0 vocabulary covers a small
minority of the public suite cleanly, which is expected and consistent
with the `sv-tests-2` census's shape — the top blockers on the smoke
sample are `AssignmentExpression:target`, `VariableSymbol:signed`,
`NamedValueExpression:signed` and `VariableSymbol:range`, i.e.
**signedness and range metadata, not exotic constructs.**

**What the re-census cannot settle** is comparability: the two corpora
share no files, so public-suite numbers are a *new baseline*, not a
delta against `docs/sv-corpus-coverage.md`. Any claim that the tier's
coverage "changed" by switching corpora would be meaningless.

### 1.7 The family registry row — corroborated twice, and CORRECTED once

`docs/family-architecture.md` landed while this charter was being
written, and it carries a PROPOSED registry row for this lane:

| language | `<Lang>` | authority | edition tokens | oracle | corpus |
| --- | --- | --- | --- | --- | --- |
| SystemVerilog | `Sv` | spec-mirror — IEEE 1800 | `SV2017`, `SV2023` — **PROPOSED** | pyslang frontend; a simulator | sv-tests-2 |

The two lanes worked independently and agree on three things, which is
worth more than either saying it alone.

* **The edition split.** The family doc records SV as *"one lane, two
  editions"* — citing -2017 for operator semantics while censusing a
  -2023 corpus. This charter found the same inconsistency from the
  other end (§2.1). **Independently corroborated; §8.5 is the
  decision.**
* **`Circuit/` is not the divider's foothold.** The family doc warns
  that *"a founding lane that goes looking in `Circuit/` will find
  calculus"* and concludes the divider's circuit side is the SV tier.
  §6.1 reached that by censusing the 25 files. **Corroborated
  empirically.**
* **An instrument in the wrong tree.** The family doc names
  `extractors/sv/census.py` as the one violation of *"instruments live
  in `harness/`"*, to fix *"when the SV lane is next open."* **The lane
  is now open**, so SV-M1 adopts it (§7 inch 7).

**And one correction this charter owed the family doc — now
RESOLVED BY RULING.** The registry row's corpus field reads
**`sv-tests-2`**, an external corpus without redistribution permission;
the charter objected that a
public repository's registry should not name a corpus its readers
cannot obtain. **Ruling §6.1 settles it:** `sv-tests-2` is citable
for measurements, redistribution is deferred, and the standing condition is
that it **stays out of public artifacts** until a further ruling. So the
row records the measurement source, and the registry's *public*
presentation is what remains gated. The IEEE PDF stays unopened
regardless — that is our own law, not a consequence of the licence
question.

**A second correction, still owed OUTWARD and not resolved by any
ruling** (§7.3): the family document records `Run σ α` as used by
*"Python (16 files) and SystemVerilog (3)"*. SV's true count is
**zero** — it uses its own `Sv.Res`, and the "3" is a bare-word match on
doc comments. The move-to-`Core` trigger is fixed on the premise that SV
is a second consumer, and it is not.

---

## 2 THE SPEC MAP — IEEE 1800

### 2.1 The versioned pair

The family directive is *versioned surfaces*. For SV the version
siblings are:

* **IEEE 1800-2023** — current. What `sv-tests-2` targets and what the
  charter treats as the reference edition.
* **IEEE 1800-2017** — the prior revision, and the edition
  `docs/sv-design-m0.md` actually cites for its 4-state operator
  semantics (§11.4.3 whole-vector collapse, §11.4.11 ternary merge).

**They are not far apart, and that is the point.** 1800-2023 is a
maintenance revision: clause numbering is stable across the core
simulation clauses, so a `-2017` citation and a `-2023` citation
usually name the same rule. The C tier's versioning problem (C99 vs
C11 vs C23 genuinely move semantics) is *milder* here — but the lane
already has a live inconsistency, citing -2017 in the design memo while
the corpus is -2023, and the charter's rule is: **cite the edition you
measured against, per claim, and never silently mix.**

No IEEE text is reproduced anywhere in this repository. Clause numbers
and paraphrases only.

### 2.2 The clause structure, classified

IEEE 1800-2023's ~40 normative clauses do **not** form one semantic
surface. Classified for the tier — this is what tells the owner which
clauses are *semantics* and which are *features*:

| class | clauses | what it means for the tier |
| --- | --- | --- |
| **Simulation semantics — THE HEART** | **4** (scheduling), 9 (processes), 10 (assignments), 11 (operators), 12 (procedural statements), 6–7 (data types/values) | must be modelled; every theorem depends on them |
| **Elaboration / static structure** | 3, 23 (modules), 25 (interfaces), 26 (packages), **27 (generate)**, 33 (configurations) | resolved *before* time starts; the `sv-0.2` symbolic mode is exactly this layer |
| **Lexical / preprocessing** | 5, 22 | frontend's job; slang already owns it |
| **Verification features** | 8 (classes), 13, 14 (clocking), 15 (IPC), 18 (constrained random), 19 (coverage), 24 (programs) | a *separate tier* — see §2.5 |
| **Assertions** | 16, 17 (checkers), Annex F | a temporal logic over the trace; its own semantic layer |
| **Structural / timing modelling** | 28 (gate-level), 29 (UDP), 30 (specify), 31 (timing checks), 32 (SDF) | legacy Verilog surface; low value, cleanly separable |
| **Foreign / API surfaces** | 34 (protected envelopes), 35 (DPI), 36–38 (VPI), 39 (assertion API), 40 (coverage API) | axiomatic boundaries, not semantics |
| **Annexes** | A (formal BNF), B (keywords), F (assertion semantics) | A and F are *gifts* — see below |

**Two annexes deserve naming.** **Annex A** is a complete formal
grammar — the SV analogue of nothing the C tier had, and a natural
completeness yardstick (*"which productions does the tier accept?"*,
exactly the shape of the Python lane's 86-production census). **Annex
F** gives concurrent assertions a formal semantics *in the standard
itself*, so clause-16 work has a normative target rather than an
interpretation.

### 2.3 THE SEMANTIC HEART: clause 4, priced

**Clause 4 (scheduling semantics) is the SV tier's centre of gravity,
and nothing else comes close.** C's semantic heart was a memory model
that had to be *invented* from prose scattered across §6.5 and Annex
J. SV's is one clause, and it is written as an operational algorithm.

The stratified event regions, per simulation time slot, in order:
**Preponed → Active → Inactive → NBA → Observed → Reactive →
Re-Inactive → Re-NBA → Postponed**, with iteration back to Active
until the time slot's events are exhausted. The PLI regions interleave.
This is what makes:

* nonblocking assignment (`<=`) mean *sample now, commit in NBA*;
* `always_comb` settle to a fixpoint within Active;
* clocking blocks and program blocks sample in Preponed and drive in
  Reactive — the whole point of clause 14 and 24;
* `$strobe`/`$monitor` see Postponed values.

**The pricing, and it is the charter's central architectural claim.**
The standard specifies the *regions* and their order, but **within the
Active region it explicitly permits the scheduler to pick any ready
process in any order.** That residual freedom is not an edge case; it
is where every race in every real design lives.

**What the tier already has, and what it does not.**
`docs/sv-design-m0.md` implements a **cycle-level** collapse of clause
4: comb-settle to fixpoint (σ-ordered) → edge phase (σ-ordered,
blocking assigns immediate) → NBA commit → comb-settle again. That is a
faithful projection of the Active/NBA split *at cycle granularity*, and
it is enough for the six M0 designs and the CV32E40P modules. The timed
loader now has the narrow positive-literal `initial`/`#d` bridge, the
Inactive delivery path, and the postponed `$strobe`/`$monitor` close
documented above; Observed / Reactive (so no clocking blocks or program
blocks) remain outside the public tier.
Unsupported timing forms remain loud.

**Price to go from the cycle collapse to the full region ladder: this
is the largest single item in the lane's future**, and it is the one
that re-opens every existing theorem, because the trace type changes
from *one snapshot per cycle* to *one per time slot with region
structure*. The charter's recommendation is to price it as its own
milestone and not to smuggle it into a feature milestone.

### 2.4 The refusal taxonomy, and how ∀-resolution generalises

The C tier fixed three causes that never pool
(`docs/c-semantics-design.md` §3.1): `unsupported` retires by climbing
a rung, `ub` **never retires because it is the product**, `libc`
retires by widening the slice. The SV mapping:

| cause | SV instance | retires by |
| --- | --- | --- |
| `unsupported` | out-of-tier construct (unsupported `initial`/`#` forms, classes, `Unsupported` nodes in the envelope) | climbing a rung |
| **`nondeterminism`** | **race: two legal schedules, two observable traces** | **NEVER — it is the product** |
| `x-propagation` | unknown value reaching an observable | never — it is a *value*, not a fault (§3) |
| `libc`-analogue | unmodelled system task (`$display`, `$random`, DPI import) | widening the slice / axiomatic boundary |
| `timeout` | comb loop, fuel exhaustion | genuine defect class, already implemented |

**The J.1-analogue, and the ruling.** C's Annex J enumerates
unspecified and undefined behaviours; SV's counterpart is not one annex
but three distinct kinds of latitude, and **they must not be pooled**:

1. **Scheduling nondeterminism** (clause 4) — the standard *grants* the
   implementation freedom. Analogous to C's **unspecified** behaviour.
2. **X-propagation** (clauses 6, 11) — *fully specified*, per-operator,
   deterministic. **Not latitude at all**, and the most common mistake
   would be to model it as such.
3. **True undefined/illegal cases** — e.g. multiple continuous drivers
   on a variable; the standard says the result is an error, not a
   value. Analogous to C's **undefined**.

Thomas's **∀-resolution ruling for unspecified behaviour generalises
directly to (1), and the SV lane is where it is already load-bearing.**
The C tier's form (`docs/c-semantics-design.md` §4.4) is *execute a
canonical order, and REFUSE where a static census cannot show the order
unobservable*. The SV form is stronger and already shipped:

```
m ⊨ P   ≡   ∀ stim σ tr, m / stim ⇓[σ] tr → P stim tr
Sv.Deterministic m — all schedules give the same observable trace
```

**Every SV theorem is already universally quantified over the schedule
oracle.** The tier does not pick a canonical order and apologise; it
proves the property *for all legal orders*, and race-freedom is a
**per-design obligation that is discharged or refuted, never assumed**.

> **CORRECTION (2026-08-22), because the sentence this replaces
> overclaimed.** It read *"race-freedom is a theorem (`Sv.Deterministic`)
> rather than an assumption"*, which invites the reading that the tier
> establishes race-freedom. **It does not, and cannot: IEEE 1800 leaves
> same-region ordering unspecified, so a racy design genuinely has no
> single outcome.** `Deterministic (d : Design) : Prop` is a
> **design-indexed predicate**, not a law — and the tier proves it for
> five designs (`adder_det`, `xsel_det`, `swap_nba_det`, `toggle_det`,
> `counter_det`) and proves its **negation** for the sixth:
> `race_blk_not_deterministic : ¬ Deterministic raceBlkDesign`.
>
> **The Lean was never wrong** — audited, no `∀ d, Deterministic d`
> exists and no proof consumes an unrestricted form. The defect was in
> this document's wording.
>
> One refinement on how the correction should be phrased: in this tier
> `Deterministic d` **IS** race-freedom — the same predicate, "all legal
> schedules agree on the trace". So the fix is *not* to write
> `RaceFree d → Deterministic d`, which would be a tautology here; it is
> that the predicate is a **premise or a per-design theorem, never a
> tier-wide conclusion**. `σ_src`
(declaration order) exists only as the *executable* default for
differential testing, and the harness demonstrably tries others —
`race_blk_one_edge` matched `sigma_rev` in today's run.

**So the ruling generalises thus: where C refuses what it cannot show
unobservable, SV proves over the whole space.** SV can afford the
stronger form because its nondeterminism is *coarse and enumerable*
(a permutation of ready processes at a scheduling point), where C's
unsequenced-modification space is tangled with aliasing. The C tier's
refusal is the weaker fallback for a harder problem — **not a different
philosophy**, and the charter records that the two lanes should not be
"harmonised" into the weaker one.

### 2.5 The verification tier — proposed as separate, **RULED IN**

Clauses 8, 13, 15, 18, 19, 24 — classes, constrained randomisation,
functional coverage, mailboxes, programs — are **half the public
suite's mass** (`uvm` is the single most common tag at 105 occurrences,
`chapter-18` is the largest chapter at 134 tests) and share almost
nothing with the simulation semantics. They need an object model, a
constraint solver, and a randomisation oracle.

**The charter proposed** that this be a distinct tier with its own
ladder, on the argument that a tier which models clauses 4/6/7/9/10/11/12
well and refuses clause 18 loudly is a *coherent* product where one that
half-models both is not.

**RULED OTHERWISE (§6.3): everything is in scope, one lane, one
ladder.** The argument above is not thereby refuted — it is answered by
sequencing instead of by separation. §8.3 puts the verification tier at
**R2 and later, after the scheduler**, precisely because clauses 8/18/19
need a clock and a process model to hang on, and R1 is what supplies
them. "Refuses clause 18 loudly" remains the correct *interim* state;
it is now a rung rather than a boundary.

---

## 3 FOUR-STATE LOGIC — the value model, priced

### 3.1 What the value model must be, and it is already built

C's value model is fixed-width two's-complement integers over 11 scalar
types, and the census forced a split (unsigned wraps, signed refuses).
**SV's is not integers at all**, and the difference is the single
largest semantic gap between the two tiers.

Already normative in `docs/sv-design-m0.md` and implemented:

```
inductive Logic | l0 | l1 | lx | lz
structure LVec where bits : Array Logic     -- LSB-first
LVec.known? : LVec → Option (BitVec w)
```

**A 4-state vector is not a number.** `LVec.known?` is the *partial*
bridge to `BitVec`, and its partiality is the whole design: a value may
be *unknown at some bit positions*, and that is an ordinary,
fully-specified state, not an error.

### 3.2 X-propagation is specified, per-operator, and NOT uniform

The facts below received independent simulation checks when M0 was built, and
they are the reason a naive "any x → x" rule is wrong:

* **Arithmetic** (`+ - * < <= >=`): any x/z bit in *either* operand
  collapses the *entire* result to x (whole-vector, clause 11.4.3).
  Never bit-precise carry.
* **Bitwise**: per-bit tables, and they are *not* strict — `0 & x = 0`,
  `1 | x = 1`. Information survives.
* **Logical `==`**: 0 if any position has both bits known and unequal;
  else x if any x/z; else 1. **Not** "any x → x".
* **Case `===`**: exact 4-state match, *always* returns 0 or 1 — the
  designated escape hatch from x.
* **`if (c)`**: true iff `c` has at least one `l1` bit; x/z-only takes
  the else branch, and an `if` with no else **holds** its target rather
  than poisoning it.
* **Ternary `c ? a : b`** with unknown `c`: evaluate both, bitwise
  merge, agreeing bits survive (clause 11.4.11) — **different from
  `if`**, and a classic source of confusion.

**Three operators are non-monotone in the information order** (`&`,
`|`, `===`), which means x-propagation **cannot** be implemented as a
generic lifting of a two-state semantics. It must be tabulated
per-operator. That is the concrete price of the value model, and it is
already paid in `LeanModels/Sv/Basic.lean`.

### 3.2.1 Case equality in M0 — 2026-10-13

Direct `===` and `!==` expressions now travel through the ordinary M0
envelope and cycle interpreter. Their operands retain the extractor's
common-width context, and the result is a definite one-bit `0` or `1` by
exact four-state comparison (`x` and `z` remain distinct). This is the same
`LVec.eqCase`/`neCase` authority used by lowered ordinary `case` statements;
there is no second comparison table. Invalid frontend compilations remain
loud through the existing extractor provenance gate.

### 3.2.2 Logical conjunction and disjunction in M0 — 2026-10-13

Direct `&&` and `||` expressions now use the ordinary M0 envelope and cycle
interpreter. Each operand first converts through the four-state truthiness rule
(`1` if any bit is `1`, `0` if all bits are known zero, otherwise `x`), then
the existing `Logic.and`/`Logic.or` tables decide the one-bit result. This is
distinct from bitwise `&`/`|` and reuses the value-core authority already used
by the self-check tier.

### 3.2.3 Standalone integral increment and decrement — 2026-10-13

In the self-check tier, standalone `value++`, `++value`, `value--` and
`--value` statements now lower to the existing blocking-assignment path. The
lowering reads the identifier once and adds or subtracts a one-bit-width
literal, so four-state unknown propagation, modulo wraparound and two-state
squashing remain those of the shared arithmetic operators. Prefix and postfix
forms have the same observable effect in statement position; their discarded
expression result is not modeled. Selected, nonintegral and otherwise invalid
targets remain loud. For-loop steps already use this same lowering, so no new
scheduler or loop mechanism is introduced.

The extractor test covers all four spellings and selected-target refusal. The
`Examples/system-verilog/increment/` fixture checks four-state wraparound in
the self-check runner, Icarus, and the value-core proof.

### 3.3 X-pessimism, and what it means for MATCH verdicts

**This is the value model's sharpest consequence for differential
testing.** Real simulators are *pessimistic* about x in some places and
*optimistic* in others, and the standard permits some of this
divergence.

* **X-pessimism**: the model yields x where a real design would settle
  to a definite value (e.g. `(a & ~a)` computed bit-blind on an unknown
  `a` gives x, though it is 0 for any concrete `a`).
* **X-optimism**: a simulator yields a definite value where the true
  set of possible behaviours is not a singleton — famously `if (x)`
  taking the else branch, which *hides* a real design bug.

The tier models the **LRM's** rules, which include the optimistic
`if`. `docs/sv-spec-surface.md` §5 already frames this as *"we model
the LRM, and prove it honestly"*.

**The verdict rule this forces, and the charter states it plainly:**

> A differential MATCH against a simulator is a check on the *model*,
> **not** a proof about the *design*. Where a trace contains x, the
> honest reading of MATCH is *"our model reproduces the LRM's
> x-behaviour, which the simulator also implements"* — never *"the
> design is correct."*

Concretely: of today's 10 green harness cases, **three are explicitly
x-carrying** (`adder_x`, `counter_xrst`, `xsel_x`) plus
`toggle_x`. Those four are the model's x-rules agreeing with Icarus's
— genuinely valuable, and *not* statements about the designs. The
sharper theorems are the x-free ones: `counter_refines` (cycle
refinement against a golden Lean model) and `swap_nba_det`
(`Sv.Deterministic`).

**Consequence for the corpus.** A conformance corpus scored purely on
MATCH will over-report. The refusal taxonomy (§2.4) must keep
`x-propagation` **out of** the fault classes — an x in a trace is a
value, and a test whose expected output is x is a *passing* test, not a
degraded one.

---

## 4 DRIVER-ARTIFACT CENSUS — **DISSOLVED by ruling §6.2**

> The census below stands as measurement; its *question* was answered by
> dissolving it. With full-spec support as the endgame, **the
> conformance suite is the fixture set** and no dedicated driver is
> wanted. `DRAM_uvm` is recorded as an optional showcase. The section's
> own conclusion — that SV has no ctwin-analogue and does not need one,
> because its oracle is a simulator — is upheld.

The C tier's driver is `tools/ctwin/sunfish.c`, a node-identical twin
of the Python corpus — which is what makes the square (A ≡ C) even
statable. **The charter's finding: SV has no ctwin-analogue, and it
does not need one — but it does need a designated driver, and today it
has three de-facto ones that were never chosen.**

### 4.1 What is already driving the lane

| artefact | provenance | licence | role today |
| --- | --- | --- | --- |
| 6 hand-written designs (`adder`, `counter`, `race_blk`, `swap_nba`, `toggle`, `xsel`) | written for this repo | repo's own | the M0 gallery; all six proved |
| 7 `t2_*` probes | written for this repo | repo's own | per-feature `sv-0.2` probes |
| 5 CV32E40P modules (`popcnt`, `ff_one`, `alu_div`, `fifo`, `register_file_ff`) | **OpenHW Group**, pinned `6033d2b1…` | **Solderpad 0.51 / Apache-2.0** | the real-RTL acceptance set |

The CV32E40P modules are the closest thing to a real driver: genuine
industrial RISC-V RTL, dual-simulator validated. **But they are
someone else's IP**, vendored as individual `.sv` files into
`Examples/system-verilog/sem2/` while their build dependencies
(`cv32e40p_pkg.sv`) are deliberately *not* vendored — which is why one
of the 18 envelopes cannot regenerate here (§0). Solderpad/Apache is
permissive, so this is a *completeness* wart, not a licensing one.

### 4.2 Choosing real artifacts

Use redistributable real RTL with a pinned source checkout. The existing
six M0 designs already round-trip and are proved, but deliberately small
examples cannot establish scaling. The CV32E40P examples exercise real
RTL and require a complete, correctly pinned third-party checkout.
Design and testbench admission remain separate: accepting a hardware
module does not imply support for its verification environment.

Do not manufacture a hand-maintained twin merely to obtain a proof
target. Verify real source artifacts through their language semantics,
using completed independent simulations for differential checks.

---

## 5 CONFORMANCE CORPUS — the recommendation, and how it was **RULED**

> **Ruling §6.1 took the other branch from the one this section leans
> toward, and did so knowingly.** `sv-tests-2` is citable for internal
> docs and proofs; open-sourcing is deferred; it stays out of *public*
> artifacts meanwhile. The per-file licence work below is therefore not
> wasted — it is what makes the public/internal split enforceable, and
> it is what the vendoring rule (`tests/**` only) still governs the
> moment anything is vendored. The IEEE PDF stays unopened either way.

Per the family law, **fetch-don't-vendor unless licences clearly
permit**. The two candidates split cleanly:

| | vendor? | why |
| --- | --- | --- |
| `sv-tests` `tests/**` | **yes — permitted** | uniform ISC, per-file SPDX, single holder, 0 contamination hits |
| `sv-tests` `third_party/**`, `tests/generated/**` | **never** | reaches GPL-2.0 (ivtest), Solderpad, unlabelled 2 504-file core |
| `sv-tests-2` | **never** | no licence at all; employer-internal; embeds the IEEE PDF |

**Recommendation, for the owner to accept or reject.** Vendor a
*pinned subset* of `sv-tests/tests/**` under a `PROVENANCE.md` carrying
the ISC text and the commit sha `4f24807…` — the same pattern
`vendor/cpython-3.9-lib-test/` already uses — and keep `sv-tests-2` as
a **fetch-only, path-configurable** corpus for the owner's private
measurement. Concretely that means `census.py`'s hard-coded
`DEFAULT_CORPUS` (§1.3) becomes a required flag or an env var, so the
instrument is honest on any host.

**Other free corpora**, noted and not pursued: Icarus's `ivtest`
(**GPL-2.0 — unusable for vendoring**), Yosys's `tests/` (ISC),
Verilator's own regression suite (its test files are largely
permissive but the harness is LGPL-3/Artistic; Verilator's suite is
*also* a genuine corpus and worth a later look). **Commercial suites
(Accellera/UVM golden, vendor conformance kits) are out of scope: no
purchases, and the charter proposes none.**

---
## 6 THE RULINGS — all six taken, 2026-08-22

The charter presented six decisions and recommended none. **The owner
ruled all six the same day.** They are recorded here verbatim, each with
what it changes.

### 6.1 The anchor corpus — `sv-tests-2` IS citable

> *"sv-tests-2 IS CITABLE (open-sourcing deferred — so: internal
> docs/proofs may cite it freely; keep it out of PUBLIC artifacts until
> he rules; the embedded IEEE PDF stays unopened per our own law
> regardless)."*

So `docs/sv-corpus-coverage.md` keeps its anchor and its numbers stand.
Three standing conditions: internal citation is free; **public
artifacts must not name it** until a further ruling; and the embedded
`ieee-1800-2023.pdf` **stays unopened**, which is our own law and not
contingent on the licence question.

**What landed under this ruling.** `extractors/sv/census.py` keeps
`sv-tests-2` as its default corpus — but by *name* through a registry,
never by a hard-coded absolute path, and the public suite is wired
beside it so the anchor is a flag. §8.1's decision-neutral half is
therefore already done: switching is `--corpus-name sv-tests`.

### 6.2 The driver artefact — DISSOLVED

> *"Driver artifact: DISSOLVED by ruling 6 — no dedicated driver; suite
> tests are the rung fixtures; DRAM_uvm noted as optional showcase
> only."*

The charter's §4 conclusion is upheld and then made moot: with full-spec
support as the endgame, **the conformance suite IS the fixture set**.
There is no ctwin-analogue and none is wanted. `DRAM_uvm` survives as an
optional showcase, not a dependency.

### 6.3 Scope — EVERYTHING, with a PLUGGABLE oracle

The scope includes the whole specification, including the verification
tier: classes, constrained randomization and assertions. Simulation
validation is pluggable when individual tools cannot run a fixture.

This reverses the charter's §2.5 suggestion that the verification tier
be a separate lane. It is one lane and one ladder.

The ruling carries a design order with it: **the oracle becomes a
parameter from day one**, with *per-test oracle attribution recorded* —
which oracle produced each expected result is **provenance**, exactly as
the C tier names the interpreter on its coverage lines. Icarus stays the
default; an alternative completed simulation is required where a tool
cannot execute a fixture. The semantics must not depend on tool availability.

This is the same lesson the census just paid for in cash: an artifact
that does not record what produced it cannot be checked later. The
census now stamps corpus, frontend family, platform and walk mode for
precisely this reason, and the harness must stamp its oracle for the
same one.

### 6.4 Clause 4 — the FULL scheduler, and EARLY

> *"Clause-4: FULL scheduler in scope, sequenced as rungs — cycle-level
> first (the divider milestone's fragment), full regions after."*

with the emphasis:

> *"modelling the scheduler is very important to have full SV support."*

§8 re-cuts the ladder around this. The charter's own pricing note — *the
region ladder re-opens every theorem* — is the argument **for** doing it
early rather than against doing it at all: the cheapest moment for a
semantics change is before the theorem estate grows.

### 6.5 Editions — BOTH, with -2023 priority

> *"BOTH editions, 1800-2023 priority: adopt the family's
> sibling-editions layout — plan the move of the dormant tier's
> edition-sensitive files under Sv/V2023/ (census WHICH files are
> edition-sensitive first, the C tier's Value.lean lesson: measure,
> don't assume)."*

So the -2017/-2023 mixing this charter found (§2.1, §1.7) becomes a
concrete cleanup with a destination. **Census first**: which files are
actually edition-sensitive is to be *measured*, not assumed. The
starting evidence is in §7 — all 7 in-Lean edition tags are `-2017`,
concentrated in `Basic.lean`, while the corpus targets `-2023`.

### 6.6 The endgame — FULL SPEC SUPPORT

> *"ENDGAME = FULL SPEC SUPPORT, like every surface. The FP-divider
> (integer rung A then HardFloat) is a MILESTONE on the ladder, not the
> endgame — position it as the clause-4 cycle-level rung's flagship
> exit."*

§6's menu of three endgames collapses: options (a) and (b) were
milestones misfiled as destinations, and (c) — the completeness ladder —
is the endgame. **The scoreboard is coverage-by-clause against the
482-entry dictionary** the public suite already ships (§1.5).

---

## 7 THE DORMANCY RECORD — what 322 commits of law did while the lane slept

The lane stopped at `db9bb3e` on **2026-07-31** and this charter opened
at `39ea9ff` on **2026-08-22**: **322 commits, 22 days.** That window is
the C arc, and it is where most of this repository's *general* law was
written. The SV tier predates all of it.

**This section exists because a dormant tier does not merely fall
behind on features — it falls behind on RULES, and rules are invisible
until someone checks.** What follows is that check.

### 7.1 What the tier already satisfies BY ITS OWN ROUTE

The most useful finding is not the retrofit list — it is that the SV
lane independently invented a good deal of what later became law, and
in two places invented it *better*.

| law (later) | SV's independent route |
| --- | --- |
| **schedule-as-parameter + executable counterexample** (family §3.6) | `ScheduleOracle` bundles a choice function *with its legality proof*; `⊨` is `∀ σ stim tr`; `Sv.Deterministic` makes race-freedom a **per-design obligation, proved or refuted** (five designs prove it; `race_blk_not_deterministic` refutes it). `race_blk/spec.lean` runs one stimulus under `σ_src` and `σ_rev` as kernel-checked `#sv_check` pairs — the family document's illustrative example, **in the tree a month early** |
| four-constructor outcome covenant (§3.2) | `Sv.Res` reproduces the covenant's *semantics* (`.timeout` is fuel exhaustion and nothing else; `.unsupported` is loud and fuel-independent) with its own short-circuit simp lemmas |
| ∃-fuel + monotonicity (§3.2) | `Obs.lean` builds the ⊑-lattice, `run_mono`, and `Runs.at_least` as `∃ f₀, ∀ F ≥ f₀, …` |
| `--compare` staleness intent (§5.4) | `--recheck`: a fixed-seed determinism check against the stored census — half the law, invented independently |
| ingester REFUSES a provenance mismatch (§1.5) | `PDesign.crossCheck` refuses the envelope when the frontend's elaboration disagrees with the ingester's — the right mechanism, keyed on a different field |
| `maybe`-gated CI with reported SKIPs (§3) | both SV harnesses were `maybe`-gated from day one, a month before it became family law |
| goal-state-as-interface | 7 `#guard_msgs`-pinned delaborators |

**Two of these are stronger than the law that later replaced them**, and
§2.4 already records why: where C refuses what it cannot show
unobservable, SV proves over the whole schedule space.

### 7.2 What needs retrofitting — measured, and ranked

| # | gap | price | note |
| --- | --- | --- | --- |
| 1 | **`extractors/sv/census.py` is an instrument in the extractor tree** | one move | The family document names this as *the* one violation in the repository, to fix *"when the SV lane is next open."* It is open. `cv32e40p_census.py` is a second, unnoticed instance |
| 2 | **`--compare`, sorted output, committed artifact** | ~25 lines | **DONE with this charter's consolidation commit** |
| 3 | **`language_version` first-class in the envelope**, ingester refuses a mismatch | one function + 21 regens | SV is the family document's *named* failure mode: "one lane, two editions, no field that says so". Ruling 6.5 makes this load-bearing |
| 4 | **`frontend.version` must be the FAMILY, not a point release** | one line | **DONE for the census** (`pyslang-11`); the envelope still stamps `11.0.0` |
| 5 | **verdict vocabulary**: MATCH / REFUSE(cause) / DIVERGE / TIMEOUT | one function each | The harnesses speak PASS/FAIL only, and conflate timeout with unsupported. Ruling 6.3's oracle attribution lands in the same edit |
| 6 | **`docs_check` coverage is ZERO for SV docs** | one marker per block | 73/73 marked blocks pass repo-wide and **none is in an SV document**; the quickstart's 6 blocks are literally what a reader types |
| 7 | **one runner process per batch** | one function + lakefile line | `diff_test.py` spawns a fresh `lake env lean --run` per (case, σ). Affordable at 10 cases, fatal at corpus scale — and ruling 6.6 makes corpus scale the point |
| 8 | **`#print axioms` on the theorem set** | one block | 1 occurrence against 98 declarations |
| 9 | **the clause manifest** — generated and checked, never hand-maintained | one file, 30-60 rows | Highest long-run value: it is simultaneously the reader's view, the cross-edition gate, and ruling 6.6's scoreboard. **Uniquely cheap here** because `conf/lrm.conf` is a ready-made 482-entry dictionary |

**Deliberately not retrofitted.** `Sv.Res` → `Core/` unification is
structural, and the family document fixes its trigger on the C tier's
M2, not on SV. `LeanModels/Sv/SV2023/` waits on §6.5's census.

### 7.3 Two corrections this lane owes OUTWARD

1. **The family document's `Run σ α` count is wrong for SV.** It records
   *"Python (16 files) and SystemVerilog (3)"*. Re-derived:
   `grep -rn ': Run\b\|Run\.' LeanModels/Sv/*.lean` → **0**. The "3" is a
   bare-word match on doc comments ("Run one comb-phase process"). SV
   uses its own `Sv.Res`; **`Run σ α` has exactly one consumer, Python.**
   This matters because the move-to-`Core` trigger is fixed on the
   premise that SV is a second consumer.

2. **The theorem count, settled with its rule** (§7.4).

### 7.4 The counting rule, stated so the number stops drifting

Two lanes reported two numbers — 86 and 93 — which is how folklore
starts. The owning charter fixes the rule:

> **RULE.** A *proof-carrying declaration* is a `theorem`, `lemma` or
> `example` at the start of a line in `LeanModels/Sv/*.lean`, allowing
> optional `@[...]` attributes and `protected`/`private`/`nonrec`/
> `scoped` modifiers before the keyword.

Under that rule, measured today:

| | count |
| --- | ---: |
| `theorem` | 93 |
| `example` | 5 |
| `lemma` | 0 |
| **TOTAL** | **98** |

**Reconciliation in one line:** the sibling lane's **93** is this count
restricted to `theorem`; this charter's earlier **86** was a regex that
required the keyword at the start of the line and so silently dropped
the 12 attribute- and modifier-prefixed declarations. **98 is the
number**; 93 is reproducible as "theorems only".

---

## 8 THE LADDER — re-cut for full-spec support

The endgame is **full spec support** (§6.6). The scoreboard is
**coverage-by-clause against the 482-entry dictionary**. What follows is
the rung order, and the one sequencing question the rulings left open.

### 8.1 THE SEQUENCING DECISION: the scheduler goes EARLY, and here is the number

Ruling 6.4 puts the full scheduler in scope; the emphasis puts it early.
The charter priced the upgrade as *"re-opens every existing theorem"*,
so the decisive metric is **how much estate a trace-type change
re-opens, and how fast that estate is growing.**

Measured today — **and re-measured in `docs/sv-r1-scheduler.md` §0,
which corrects this table**. The figures first published here were
scoped wrong twice: they counted only `LeanModels/Sv/` and their regex
missed the `⊨`/`⊑` surface forms, so they excluded every theorem about
an actual design. The corrected estate:

| estate | proof-carrying | trace-shaped |
| --- | ---: | ---: |
| `LeanModels/Sv/` | 98 | 61 |
| `Examples/system-verilog/` | 133 | 95 |
| **TOTAL** | **231** | **156 (68%)** |

*(As first published: "50 of 98, 51%".)*

**Two thirds of the estate is trace-shaped, and it is the part that
grows with every rung.** The correction does not weaken the ordering
below — it strengthens it, and R1's design then makes the number nearly
moot by routing all 156 through a single adequacy lemma
(`docs/sv-r1-scheduler.md` §5). Under the region upgrade the trace type changes from *one
snapshot per cycle* to *one per time slot with region structure*, so
those 50 re-open. Every construct rung completed first adds to that 50.

**Decision, and it follows the emphasis:** *the full scheduler is the
rung immediately after consolidation.* Doing breadth first would buy
clause coverage at the cost of compounding the one refactor that touches
half of everything — and under the doctrine the scheduler **is** the
tier's definition, because the `∀ stim σ tr` quantifier that every
theorem is stated under ranges over clause 4. A tier whose central
quantifier ranges over a placeholder is not a tier that has defined
correctness completely.

### 8.2 The divider exemplar — both orders priced, and the choice

Ruling 6.6 makes the FP divider *"the clause-4 cycle-level rung's
flagship exit"*, which sits in tension with 8.1's ordering. Priced both
ways:

**Order A — divider first, stated scheduler-parametrically.** The
good news: **∀-over-σ is already free.** Every SV theorem is stated as
`∀ stim σ tr, Runs d σ stim tr → P`, so schedule-parametricity is not
something to add — it is the tier's existing shape. What is *not* free
is **trace-type stability**: the divider's observable is a cycle-indexed
projection, and after the upgrade "cycle" is a derived notion.
Parametricity therefore costs one abstraction function
`cycleOf : Trace → CycleTrace` plus an **adequacy lemma** saying the
region semantics projects onto the cycle semantics for designs in the
cycle-level fragment. Price: the adequacy lemma is the real work — it is
the theorem that the two models agree, and it cannot be cheap because it
is exactly the content of the upgrade. Divider theorems then survive
untouched.

**Order B — scheduler first, divider after.** Zero divider theorems
re-open, because none exist yet. The adequacy lemma is still wanted (see
8.3) but is no longer on the divider's critical path.

**Chosen: Order B, with one exception.** The adequacy lemma has to be
written either way, and writing it *before* there is a divider estate to
protect means writing it once against 50 declarations rather than twice
against 50-plus-N. The exception is **rung A, the integer divider**: its
SV side is already ingested and in-tier, so if a demonstrable theorem is
wanted before the scheduler lands, `cv32e40p_alu_div` is the cheap one
to state — and it should be stated *through* `cycleOf` from the first
line, so it is Order-A-shaped and survives.

### 8.3 The rungs

**R0 — CONSOLIDATION. (Largely landed.)** The four instrument defects
closed, the round-trip gate green at 18/18, the census committable and
`--compare`-checkable. Remaining: retrofits 1, 5, 6, 7 of §7.2, and
`language_version` (retrofit 3) which ruling 6.5 makes load-bearing.

**R1 — THE SCHEDULER. Clause 4 in full.** **Designed in
[docs/sv-r1-scheduler.md](sv-r1-scheduler.md)** — the region census, the
determinism boundary, the Lean shape, the `cycleOf` adequacy lemma, the
divider's statement shape, and nine priced inches. Census-first, per the
ruling:

1. **Census the region semantics before modelling it** — the nine
   regions (Preponed, Active, Inactive, NBA, Observed, Reactive,
   Re-Inactive, Re-NBA, Postponed) plus the PLI regions, which are in
   scope under 6.3. Enumerate, for each: what enters it, what may
   reorder within it, and what the standard *fixes*.
2. **Draw the determinism boundary explicitly** — what within a region
   is ∀-quantified versus ordered. This is the `ScheduleOracle`'s new
   contract and the single most important artifact of the rung.
3. **Map the existing cycle model onto it.** The upgrade must be an
   **extension** where the cycle model is a faithful projection, and a
   **supersession-with-adequacy** where it is not — and *never a silent
   replacement*. The definition-change discipline applies to our own
   tiers: if `cycleStep` stops meaning what it meant, that is a recorded
   change with an adequacy lemma, not a quiet edit.
4. Then the semantics, then re-establish the 50 trace-shaped
   declarations through the projection.

Unlocks `initial`, `#` delays, clocking blocks (cl. 14), program blocks
(cl. 24) — and therefore most of the verification tier's *timing*.

**R1-exit — THE DIVIDER FLAGSHIP.** Integer first
(`cv32e40p_alu_div`, already ingested), then IEEE 754 via Berkeley
HardFloat's `divSqrtRecFN` (§6.2's obstacles stand: the `recFN`
recoding, and it is Verilog not SV). Gated on the shared SoftFloat spec
layer, which is not SV work.

**R2..Rn — BREADTH BY CLAUSE**, ordered by the census's own priority
queue rather than by taste. Today's blockers on the public suite are
**signedness and range metadata** (`VariableSymbol:signed`,
`NamedValueExpression:signed`, `VariableSymbol:range`) — unglamorous,
and the highest-frequency thing in the way. The verification tier
(cl. 8, 18, 19) enters here, after R1 has given it a clock to hang on.

**Scoreboard, every rung:** clauses covered / 482, generated and
checked, never hand-maintained.

---

## 9 WHAT REMAINS OWED

The six decisions are taken. Three standing obligations remain.

1. **Completed per-fixture validation.** The simulation backend is a
   parameter. Tool availability alone never establishes an execution
   result, and unsupported fixtures need a named outcome.

2. **Operator-level evidence.** Icarus reproduces the 10 harness cases,
   but that does not by itself re-check every four-state operator table.
   No new claim may call a table independently verified without a run.

3. **External corpus sources stay out of public artifacts** until the
   open-sourcing ruling, and **the IEEE PDF stays unopened**. Both are
   standing conditions of ruling 6.1, not one-time checks.

---

## 10 WHAT LANDED WITH THIS CHARTER

### Symbolic continuous concatenation targets — 2026-10-19

The semantic `sv-0.2` surface now admits continuous assignments whose LHS is
a nested concatenation of direct scalar, constant bit-select, or constant
part-select leaves. Nested concatenations flatten in source order to
`ConcatTarget`; the existing comb-settle path samples the RHS once and writes
the corresponding MSB-to-LSB windows into the existing packed-vector state.
Dynamic, aggregate, duplicate, aliased, effectful, and legacy/self-check
concatenation targets remain loud. The `sem2/concat_assign` fixture is carried
through the symbolic runner and the `concat_assign` differential case.

### Symbolic constant selected continuous drivers — 2026-10-19

Continuous assignments to disjoint constant bit/part-select windows are now
carried by the same `Design2` comb-settle path. The `selected_assign` fixture
checks source-order settling, live low-window updates, and four-state
propagation while retaining the existing packed-vector storage. Dynamic,
effectful, overlapping, aggregate, and legacy/self-check selected drivers
remain loud.

The `bit_select_assign` fixture separately pins the one-bit form, including a
selected source bit, an undriven x-state remainder, and x propagation through
the scalar driver. It uses the same packed-vector window representation and
does not add a scheduler or driver-resolution rule.

### Symbolic packed-struct member windows — 2026-10-19

Direct integral members of untagged packed structs and unions now lower to
fixed `PartSel` windows over one packed vector in the symbolic continuous
assignment path. `packed_member_assign` checks struct field writes and reads;
`packed_union_assign` checks same-width alternate-field aliasing. Tagged
structs/unions, unpacked or dynamic members remain loud; nested untagged union
chains are covered by the recursive window section below. These semantic
fixtures do not claim a legacy census gain or simulator agreement.

### Symbolic packed-struct typedef metadata — 2026-10-19

Typedefs naming an untagged packed struct are now treated as compile-time
metadata in the same narrow path. `packed_member_typedef` and
`packed_union_typedef` check that canonical vector widths survive alias
removal. Tagged, tagged-union and unresolved type aliases remain loud, and the
semantic fixtures do not claim a legacy census gain or simulator agreement.

### Symbolic nested packed-member windows — 2026-10-19

Nested untagged packed-struct member chains now accumulate their fixed
declaration offsets and lower to windows over the outer vector. The
`packed_member_nested` fixture checks both inner fields and x propagation;
nested untagged packed unions use the same flat alias windows, while tagged and
other aggregate paths remain loud. This is a symbolic fixture result only, with
no legacy census or simulator-agreement claim.

### Symbolic nested packed-union alias windows — 2026-10-20

Nested untagged packed-union member chains now accumulate their fixed
declaration offsets and lower to `PartSel` windows over the outer vector.
The focused symbolic tests check alternate-field alias visibility and the
existing overlap guard rejects conflicting symbolic drivers. Dynamic/effectful,
tagged and unpacked aggregate paths remain loud; no aggregate store, driver
resolution or scheduler is added.

### Symbolic literal indexed part-select windows — 2026-10-19

Literal indexed part-selects now normalize to fixed `PartSel` bounds when their
window is in range. `indexed_part_assign` checks both `base +: width` and
`base -: width` through the existing comb-settle path. Dynamic or
parameter-dependent bases and out-of-range windows remain loud; no new storage
or scheduler is introduced and no legacy census or simulator-agreement claim
is made.

### Symbolic noncanonical packed-range windows — 2026-10-20

Simple literal part-selects on noncanonical packed ranges now map their source
and destination labels to zero-based LVec offsets before entering the existing
window executor. `noncanonical_part_assign` checks a `[10:3]` range and
four-state propagation. Dynamic, indexed and out-of-range forms remain loud;
this adds no storage or scheduler and makes no legacy census or
simulator-agreement claim.

Literal bit-selects on the same noncanonical ranges now use the corresponding
zero-based `BitSel` offsets. `noncanonical_bit_assign` checks the endpoint
mapping and x propagation; dynamic noncanonical indices remain loud because
the runtime vector state carries no declaration-label table.

### Symbolic overlapping-driver guard — 2026-10-20

Separate symbolic continuous assignments now reject statically overlapping
constant windows on one base. The conflicting process becomes `Unsupported`,
so process order cannot masquerade as IEEE driver resolution. Dynamic windows
remain outside this check and no resolution or scheduler rule is added.

### Symbolic packed-member concatenation — 2026-10-20

Direct fixed members of an untagged packed struct may now be concatenation
leaves. `packed_member_concat` checks one sampled RHS split into disjoint
member windows and read back through those members. Overlapping union-member
leaves remain loud under the same window guard; no aggregate store or new
scheduler is introduced.

### Symbolic packed-member subranges — 2026-10-20

Constant simple subranges inside packed members now flatten by adding the
member's fixed offset to the local slice offset. `packed_member_subrange`
checks the resulting outer-vector window and x propagation. Dynamic nested
indices and non-simple selections remain loud; no aggregate store or scheduler
is added.

### Symbolic packed-member bit selects — 2026-10-20

Literal bit-selects inside packed members now flatten by adding the member's
fixed offset to the local bit offset and emitting a one-bit outer-vector
window. `packed_member_bit` checks the write/read path and x propagation.
Dynamic nested indices and non-simple selections remain loud; no aggregate
store or scheduler is added.

### Symbolic packed-union member subranges — 2026-10-20

Literal subranges of direct members of an untagged packed union now flatten to
fixed windows in the union's shared vector. `packed_union_subrange` checks the
write through one field and read through an alternate field, including x
propagation. Tagged, nested and dynamic union paths remain loud; no driver
resolution, aggregate store or scheduler is added.

### Symbolic packed-union member bit selects — 2026-10-20

Literal bit-selects of direct members of an untagged packed union now flatten
to one-bit windows in the union's shared vector. `packed_union_bit` checks the
write through one field and read through an alternate field, including x
propagation. Tagged, nested and dynamic union paths remain loud; no driver
resolution, aggregate store or scheduler is added.

### Symbolic indexed packed-member windows — 2026-10-20

Literal indexed part-selects of direct packed-struct members now normalize to
fixed outer-vector windows when the member range is canonical and the selected
window is in bounds. `packed_member_indexed` checks both `+:` and `-:` forms
with four-state propagation. Dynamic, parameter-dependent, noncanonical and
effectful nested selections remain loud; no aggregate store or scheduler is
added.

### Symbolic indexed packed-union windows — 2026-10-20

Literal indexed part-selects of direct members of an untagged packed union now
use fixed windows in the union's shared vector. `packed_union_indexed` checks
both `+:` and `-:` forms through an alternate field, including x propagation.
Tagged, nested, dynamic, parameter-dependent, noncanonical and effectful union
paths remain loud; no driver resolution, aggregate store or scheduler is
added.

### Symbolic noncanonical packed-member subranges — 2026-10-20

Literal simple subranges of packed members now map declaration labels to outer
vector offsets even for noncanonical member ranges when the selected labels
follow the declared direction. `noncanonical_member_subrange` checks a
`[10:9]` slice inside `[10:7]` with four-state propagation. Direction-
mismatched, dynamic, indexed and effectful nested selections remain loud; no
aggregate store or scheduler is added.

### Symbolic noncanonical packed-union subranges — 2026-10-20

Literal simple subranges of direct noncanonical packed-union members now map
declaration labels to windows in the shared vector. `noncanonical_union_subrange`
checks alias visibility and four-state propagation for `[10:9]` inside
`[10:7]`. Direction-mismatched, dynamic, indexed and effectful union paths
remain loud; no driver resolution, aggregate store or scheduler is added.

### Symbolic noncanonical packed-member bit selects — 2026-10-20

Literal bit-selects of noncanonical direct packed members now map declaration
labels to one-bit outer windows. `noncanonical_member_bit` checks the `[10]`
select inside `[10:7]` with four-state propagation. Dynamic and effectful
nested indices remain loud; no aggregate store or scheduler is added.

### Symbolic noncanonical packed-union bit selects — 2026-10-20

Literal bit-selects of direct noncanonical packed-union members now map labels
to one-bit windows in the shared vector. `noncanonical_union_bit` checks the
`[10]` select inside `[10:7]` through an alternate field with x propagation.
Dynamic and effectful union indices remain loud; no driver resolution,
aggregate store or scheduler is added.

### Symbolic typedef packed-member indexed windows — 2026-10-20

Indexed slices through an untagged packed-struct typedef now use the same
fixed member windows after alias erasure. `typedef_member_indexed` checks the
`+:` form and four-state propagation. Tagged, unresolved, dynamic and
effectful alias paths remain loud; no type table, aggregate store or scheduler
is added.

### Symbolic typedef packed-union indexed windows — 2026-10-20

Indexed slices through an untagged packed-union typedef now retain shared-vector
aliasing after compile-time alias erasure. `typedef_union_indexed` checks the
`+:` form through an alternate field with four-state propagation. Tagged,
unresolved, dynamic and effectful alias paths remain loud; no type table,
driver resolution, aggregate store or scheduler is added.

### Symbolic noncanonical typedef member subranges — 2026-10-20

Simple subranges through an untagged packed-struct typedef now retain
noncanonical declaration-label offsets after alias erasure.
`noncanonical_typedef_subrange` checks `[10:9]` inside `[10:7]` with
four-state propagation. Direction-mismatched, dynamic, indexed and effectful
alias paths remain loud; no type table, aggregate store or scheduler is added.

### Symbolic noncanonical typedef-union subranges — 2026-10-20

Simple subranges through an untagged packed-union typedef now retain
noncanonical declaration-label offsets and shared-vector aliasing after alias
erasure. `noncanonical_typedef_union_subrange` checks `[10:9]` inside `[10:7]`
with four-state propagation. Direction-mismatched, dynamic, indexed and
effectful union aliases remain loud; no type table, driver resolution,
aggregate store or scheduler is added.

### Symbolic noncanonical typedef-member bit selects — 2026-10-20

Literal bit-selects through an untagged packed-struct typedef now retain
noncanonical declaration-label offsets after alias erasure.
`noncanonical_typedef_bit` checks `[10]` inside `[10:7]` with four-state
propagation. Dynamic and effectful alias indices remain loud; no type table,
aggregate store or scheduler is added.

### Symbolic noncanonical typedef-union bit selects — 2026-10-20

Literal bit-selects through an untagged packed-union typedef now retain
noncanonical declaration-label offsets and shared-vector aliasing after alias
erasure. `noncanonical_typedef_union_bit` checks `[10]` inside `[10:7]` through
the alternate field with x propagation. Dynamic and effectful union aliases
remain loud; no type table, driver resolution, aggregate store or scheduler is
added.

### Symbolic nested packed-member indexed windows — 2026-10-20

Indexed selections of final members in nested untagged packed-struct chains
now accumulate fixed declaration offsets before emitting an outer window.
`nested_member_indexed` checks the `+:` form with four-state propagation.
Nested unions, direction mismatches, dynamic and effectful paths remain loud;
no aggregate store or scheduler is added.

### Symbolic nested packed-member bit selects — 2026-10-20

Literal bit-selects of final members in nested untagged packed-struct chains
now use accumulated fixed declaration offsets. `nested_member_bit` checks the
bit window with four-state propagation. Nested unions, dynamic and effectful
paths remain loud; no aggregate store or scheduler is added.

### Symbolic nested noncanonical packed-member subranges — 2026-10-20

Simple subranges of noncanonical final members in nested untagged packed
structs now combine recursive and local declaration offsets before lowering.
`nested_noncanonical_subrange` checks `[10:9]` inside `[10:7]` with four-state
propagation. Direction mismatches, dynamic, indexed and effectful paths remain
loud; no aggregate store or scheduler is added.

### Symbolic nested noncanonical packed-member bits — 2026-10-20

Literal bits of noncanonical final members in nested untagged packed structs
now combine recursive and local declaration offsets before lowering.
`nested_noncanonical_bit` checks `[10]` inside `[10:7]` with four-state
propagation. Dynamic and effectful paths remain loud; no aggregate store or
scheduler is added.

### Symbolic nested packed-member concatenations — 2026-10-20

Nested fixed member selections may now be concatenation leaves. Their
recursive windows retain one sampled RHS and existing MSB-to-LSB splitting;
`nested_member_concat` checks disjoint slices and x propagation. Dynamic,
aliased, duplicate, overlapping and effectful leaves remain loud; no aggregate
store or scheduler is added.

### Symbolic typedef nested packed-member concatenations — 2026-10-20

Nested fixed member concatenations now retain their recursive windows through an
untagged packed-struct typedef after alias erasure. `typedef_nested_concat`
checks one sampled RHS and x propagation. Tagged, unresolved, dynamic,
duplicate, overlapping and effectful alias leaves remain loud; no type table,
aggregate store or scheduler is added.

### Symbolic nested noncanonical packed-member concatenations — 2026-10-20

Nested concatenation leaves may now use in-direction noncanonical final member
ranges. Recursive and local declaration offsets combine before lowering;
`nested_noncanonical_concat` checks disjoint `[10:9]` leaves and x propagation.
Direction mismatches, dynamic, duplicate, overlapping and effectful leaves
remain loud; no aggregate store or scheduler is added.

### Symbolic fixed-unpacked array cells — 2026-10-20

One-dimensional fixed-unpacked integral declarations without initializers now
flatten into ordinary symbolic vector declarations, one per constant index.
`fixed_array_element` checks a write to `arr[0]` and a nested bit read from the
same cell, including four-state propagation. Dynamic and out-of-range indices,
nested or aggregate arrays, and array initializers remain loud; the semantic
tier adds no aggregate store or dynamic index executor and makes no legacy
census or simulator-agreement claim.

### Symbolic fixed-array cells through packed typedefs — 2026-10-20

Plain untagged packed integral typedefs are now erased as compile-time metadata
when they name the element type of an admitted fixed-unpacked array. The
`typedef_fixed_array_element` fixture checks that canonical element ranges
survive on `arr[0]`/`arr[1]` and that a constant cell write and nested read
propagate four-state values. Signed, 2-state, unresolved and aggregate aliases
remain loud; no nominal type table or aggregate storage is added.

### Symbolic enum-valued fixed-array cells — 2026-10-20

Ordinary four-state enum element types now retain their `TypeRef` metadata when
an admitted fixed-unpacked array is flattened into vector cells. The
`enum_fixed_array_element` fixture writes an enum member to `arr[0]` and reads
the cell through an ordinary two-bit output. Signed, two-state and aggregate
enum storage remain loud; no enum runtime table or aggregate store is added.

### Symbolic packed-aggregate fixed-array member windows — 2026-10-20

Untagged packed struct and union element types now flatten into fixed-width
array cells, and constant member accesses through those cells reuse the
existing declaration-offset `PartSel` windows. `packed_aggregate_array_member`
checks a struct field write/read and a union alternate-field read. Tagged,
nested-unpacked and dynamic aggregate paths remain loud; no aggregate runtime
store or member table is added.

### Symbolic fixed-array initializer cells — 2026-10-20

An admitted one-dimensional fixed-unpacked array may now carry a pure exact
assignment-pattern initializer. Positional, elaborated keyed/default and exact
replicated patterns are lowered into the same independent symbolic cells as
later reads and writes; `fixed_array_initializer` checks the resulting `0001`,
`xxxx` trace. Wrong-length, effectful, nested and packed-aggregate initializer
patterns remain loud; no aggregate store or runtime pattern evaluator is added.

### Symbolic fixed-array cells in concatenation targets — 2026-10-20

Constant cells of admitted fixed-unpacked arrays may now be leaves of a
symbolic concatenation target. `fixed_array_concat_target` checks one sampled
source split across `arr[0]` and an output bit, then reads the cell back with
four-state propagation. Dynamic, aliased and overlapping array leaves remain
loud; the existing flat vector storage and comb-settle path are reused.

### Symbolic noncanonical packed slices inside fixed-array cells — 2026-10-20

Constant packed selections are now composed after cell lowering. The
`fixed_array_noncanonical_slice` fixture maps `[10:9]` on a `[10:7]` element to
the `[3:2]` window of `arr[0]`, preserving x propagation through the existing
`PartSel` executor. Dynamic or effectful packed bounds remain loud; no range
table, aggregate storage or scheduler is introduced.

### Symbolic reversed fixed-unpacked ranges — 2026-10-20

Descending unpacked ranges now have a pinned symbolic boundary: emitted cells
follow declaration order while literal labels retain their own names.
`fixed_array_reverse_range` checks `[1:0]`, the `arr[0]` write/read pair and
four-state propagation. No ordinal remapping, aggregate storage or scheduler
behavior is introduced.

The charter itself, backlog §L60, and — in the consolidation commit that
followed it — `harness/sv_round_trip.py`, a rebuilt
`extractors/sv/census.py`, and `docs/sv-construct-census.json`.

**Every headline is a run**: the harness 10/10 green vs Icarus 12.0; the
round-trip **18/18 byte-identical, 3 documented SKIPs**; the build
3 690/3 693 jobs with zero compilation errors and all 14
`LeanModels.Sv.*` built (two Python-tier targets SIGTERMed under
contention — a resource kill, not a proof failure); **98** proof-carrying
declarations under §7.4's rule, 0 `sorry`, 0 `native_decide`; the
frontend gap and its one-minute fix; the gitignored census; the dead
corpus path; the corpus disjointness; the licence censuses; the pyslang
SIGTRAP and the `Pool` hang it caused; and the full 717-file public
census now completing in **1.0 s** where it previously never completed
at any job count.

**THREE corrections the charter made to itself**, all kept visible
because instrument faults are findings:

1. The first round-trip run reported 12 failures that were the
   *charter's* invocation error — **read the mode out of the artefact.**
2. §1.6 began by asserting that switching the anchor corpus was *"a
   licensing decision, not an engineering one"*; running the instrument
   refuted it.
3. **The 18th envelope was never broken.** The charter published
   *"17 of 18, 1 absent input"* and blamed a missing `cv32e40p_pkg.sv`.
   Wrong on both count and cause: the file
   `cv32e40p_register_file_ff.sv` declares module
   `cv32e40p_register_file`, so a `--top` derived from the *filename*
   could not resolve it. Read from the envelope, it regenerates
   byte-identically with no external checkout. **18 of 18.** The
   plausible-but-unverified diagnosis survived one whole publication,
   which is the argument for the gate that now runs it.

**Not one of the three was visible without executing the thing.** That
is the entire case for census-first, and this lane has now paid for it
three times.


### Type-directed packed selected reads — 2026-10-20

Legacy selected reads now accept supported two-state predefined integers and
packed scalar vectors, plus whole untagged packed structs and unions. Whole
packed aggregates have the implicit descending `[n-1:0]` view (§§7.2.1, 7.3.1).
The existing selected-read operation supplies each invalid position as `x`;
the lowering applies the existing two-state conversion to the selected RESULT
when the whole source is two-state (§11.5.1). This gives zero for unknown or
out-of-range indices while preserving the valid part of partially overlapping
reads. Mixed-field aggregates follow their whole four-state type, retaining
x/z even when some fields are declared `bit`. Selected results remain unsigned.

`selected_types` checks bit, simple-part and both indexed directions, signed
negative and unknown indices, partial overlap, whole structs/unions, mixed
fields, ascending constant labels, predefined integers and unsigned widening.
Three kernel theorems cover arbitrary source values or bits, are tied to the
real extracted assignments, and include the distinction between two-state and
mixed-state partial overlap. Its full output and 34 newly clean time-zero
corpus files agree with completed simulator runs in value-preserving mode. One additional timed NBA-loop file
agrees through the existing scheduler; two other newly clean files remain
loud in the time-zero runner (delay and continuous-process limits). The
value-preserving mode is material: default-mode probes collapse partial invalid reads to an entirely
unknown/zero result; no default-mode agreement is claimed for those probes.

The paired **22,035**-path census moves **3,018 → 3,054 clean** and
**18,951 → 18,915 partial**, with **66 include skips**, zero extraction errors
and **37 clean gains / one clean loss**. The loss corrects an earlier false
admission: named string control escapes `\a`, `\v` and `\f` disagree between
frontend decoding and simulator output, and now refuse before constant
resizing can hide them. Escaped backslashes and numeric byte escapes retain
their distinct admission. This is extraction coverage; runtime coverage is
the separate completed comparison above. Tagged/unpacked aggregates,
multidimensional source elements, dynamic noncanonical ranges, unmodelled effects and the
existing member-select limits stay loud. The symbolic selected-read surface
is unchanged. No value evaluator, storage or scheduler operation was added.


### Preserve time-zero queries at the timed boundary — 2026-10-20

The self-check envelope's `time_zero` literal marker now survives ingestion
as `SelfCheck.Design.requiresTimeZero`. The timed loader rejects any such
design before constructing a scheduler world. The existing time-zero runner
continues to evaluate the query as zero. This closes a boundary leak: a
delayed `$time` expression formerly reached the timed executor as an ordinary
zero constant. Dynamic clock queries remain outside this surface tier.

`time_boundary` checks the real extracted delayed, nested and declaration-
initializer queries, plus an ordinary zero literal. The marker is retained
through all three query shapes; all three refuse at the timed boundary.
The ordinary literal still executes after its delay, and `time_zero` still
runs at time zero. A kernel theorem excludes restricted designs at every
fuel. Completed simulator transcripts distinguish delayed time, nested time
arithmetic, a sampled initializer and a constant literal; rejected queries
are reported as refusals, not agreement.

A fresh paired census on the same **22,035** paths has no extraction changes:
**3,054 clean**, **18,915 partial**, **66 include skips**, zero errors.
No extractor, expression evaluator, clock or scheduling rule changed. The
restriction is conservative even if a particular marked initializer would
happen to be evaluated at time zero in a timed program.


### Local fixed-unpacked array declarations — 2026-10-20

One-dimensional fixed-unpacked arrays with integral or packed-vector elements
now lower to independent vector cells (§7.4.1, at most 1,024 cells). Static
local cells follow the §6.21 lifetime rule and are hoisted into
module declaration state and retain mutations across repeated block entries;
automatic cells are emitted as existing `LocalDecl` cells and reinitialize at
each entry. Generated storage names include the declaration source identity so
same-named declarations in separate scopes cannot alias. Closed pure static
initializers preserve initialization ordering; source-dependent or effectful
static initializers remain loud. Existing positional/keyed/default patterns,
copy and slice lowering, streaming cells, and two-state conversion are reused;
multidimensional, aggregate, dynamic and unresolved-lifetime forms remain
outside the tier.

The authored `local_arrays` fixture prints `entry 4 4`, `entry 5 4`, and
`entry 6 4`, and its fixture-bound Lean proof checks the static update and
automatic initializer paths. A paired **22,035**-path census gains **29 clean
files** with no losses: **3,054 → 3,083 clean**, **18,915 → 18,886 partial**,
**66 include skips**, and zero extraction errors. All 29 complete transcripts
match the independent simulator output. Fixed-array inequality now joins the
per-cell `!=`/`!==` results with `||`; equality continues to use `&&`.

### Pure integral membership — 2026-10-20

IEEE 1800-2023 §11.4.13 `inside` expressions now lower in the self-check
surface to the existing wildcard equality, inclusive order comparisons and
three-valued logical conjunction/disjunction. The frontend's common operand
width and signedness apply before the unsigned one-bit result is extended
in its surrounding context. A scalar set item uses `==?`; a colon range
uses `subject >= lower && subject <= upper`. Single dollar endpoints use
the propagated integral representation's minimum or maximum. Reversed
ranges and unknown subjects retain the existing comparison rules.

One-dimensional fixed-unpacked arrays and constant slices reuse their
flattened cells, with the same common signed or unsigned extension. All
source operands must be pure before reads are duplicated. Nested pure
membership is admitted. Effects, nonintegral values, unsupported storage,
tolerance syntax and symbolic-mode membership remain loud. Frontend errors,
including a range unbounded at both ends, refuse the design. No evaluator,
storage model or scheduling rule is added.

The authored `inside` fixture checks signed/mixed widths, wildcard
uncertainty and definite-match dominance, inclusive/reversed/unknown bounds,
dollar limits, signed/unsigned array cells, enums and nested membership.
Its fixture-bound kernel theorems establish definite-match dominance and
all-wildcard membership for arbitrary subject vectors. A paired **22,035**-
path census gains **38 clean files** with no losses: **3,083 → 3,121 clean**,
**18,886 → 18,848 partial**, **66 include skips**, and zero extraction errors.
All 38 newly clean files execute and match complete independent transcripts.

### Pure logical implication — 2026-10-20

IEEE 1800-2023 §11.4.7 integral `a -> b` now lowers to `!a || b`.
Each operand keeps its self-determined width and truth conversion; the
result is unsigned and one bit before surrounding extension. Frontend AST
nesting preserves right associativity and conditional precedence. Only pure,
fully admitted integral operands are accepted, including nested implication.
Calls, increments, assignments and unsupported values remain loud even when
short-circuiting could skip them. Constant folding cannot bypass admission,
and a frontend error refuses the design in either envelope mode.

Both symbolic compilers use their existing logical vocabulary. M0's
previously missing `land`/`lor` compilation clause now preserves the same
self-determined operand widths as the second compiler; both call existing
four-state value rules. No evaluator or scheduling rule is added. Equivalence
`<->` remains loud, including constant contexts: the independent simulator
rejects it in the expression contexts probed here.

The authored `implication` assignment is loaded as a literal AST. Its kernel
proofs establish false-antecedent and true-consequent dominance at arbitrary
source widths, and check both symbolic compiler shapes in a wider result
context. Both compiler paths match all 16 scalar input pairs repeated at
widths 1, 4 and 65. A separate values fixture checks vector truth, unknowns,
result extension, wider arithmetic and associativity.

A paired **22,035**-path census gains **7 clean files** without losses:
**3,121 → 3,128 clean**, **18,848 → 18,841 partial**, **66 include skips**,
zero extraction errors. Six newly clean files execute and match complete
independent transcripts. The seventh combines a continuous assignment with
a delay and remains a runtime refusal: neither the initial-only self-check
runner nor the timed loader admits that process combination. It is an
extraction gain, not an execution agreement.

### Integral formatted input — 2026-10-20

The legacy/self-check tier now admits direct blocking assignments of
`$sscanf` over pure packed input, literal formats and integral packed
outputs. The shared pure scanner supports `%b/%o/%h/%x/%d/%c/%s/%v`,
suppression, positive widths, whitespace, literals and `%%`. Input is
sampled once; successful outputs copy back left to right, later selectors
see earlier writes, unmatched destinations stay unchanged, and the return
count is assigned last. Existing packed-target rules retain neighboring
bits and two-state conversion. The timed stepper delegates the new leaf to
the same interpreter; no scheduler changes. General strings, real outputs,
other contexts/formats, excess arguments, effects and symbolic scanning
remain loud. Unknown packed input and diagnostic-bearing failures are
explicit runtime boundaries. Details: [formatted input](sv-formatted-input.md).

The paired **22,035**-path census gains **34 clean files** without losses:
**3,128 → 3,162 clean**, **18,841 → 18,807 partial**, **66 include skips**,
zero extraction errors. Thirty newly clean files execute and match complete
independent transcripts. Four remain runtime refusals: two unknown-input
diagnostics, one reduction over a selected slice, and one delay-bearing
copyback fixture. These four are extraction gains only. The authored
fixtures separately check ordered/partial copyback and integral conversion
edges, including sign/underscore field-width consumption and strength input.

### Numeric enumeration methods — 2026-10-20

IEEE 1800-2023 §6.19.5 `first`, `last`, `num`, `next` and `prev`
now lower in the legacy/self-check surface using the bound declaration-order
member table. Endpoints and traversal results retain the enum's width and
signedness; `num` returns a signed 32-bit count. Traversal uses the omitted
step of one or the frontend's unsigned two-state 32-bit argument conversion.
Steps wrap modulo the member count, including negative, wide and unknown
source counts after that conversion.

Exact case equality identifies members, including named x/z values. An
unlisted receiver returns the enum base type's default for every step,
including zero: all x for a four-state base and zero for a two-state base.
The methods never mutate the receiver. Pure packed-field and fixed-array-cell
receivers reuse the existing reads. Source purity is checked before folding
endpoints or duplicating traversal reads. Effects, unsupported storage,
frontend errors, string-valued `name()` and symbolic-mode methods remain
loud through surrounding conversions.

Lowering uses existing literals, case equality, conditional expressions and
unsigned remainder. Declaration indices are computed during extraction, so
there is no overflowing runtime index addition. No evaluator, storage model
or scheduling rule changed.

The authored `enum_methods` fixture checks sparse declaration order,
nonmembers, named x/z values, step conversion, nested calls, packed fields,
array cells, generated members and signed result extension. Its complete
transcript matches an independent simulator run. Fixture-bound kernel proofs
establish the default for arbitrary nonmembers and the first declaration's
successor. A paired **22,035**-path census gains **24 clean files** without
losses: **3,162 → 3,186 clean**, **18,807 → 18,783 partial**, **66 include
skips**, zero extraction errors. Twenty-two gains match complete independent
transcripts. Two delay-bearing files remain runtime refusals: the self-check
runner has no scheduler, and the timed loader rejects their time-zero-only
`$time` lowering. Those two are extraction gains only.

### Pre- and post-test procedural loops — 2026-10-20

IEEE 1800-2023 §§12.7.4–12.7.5 `while` and `do…while` now retain their
pure integral condition and body in the legacy/self-check envelope.
`while` tests before every body; `do…while` enters the first body before
testing. A known one bit admits the body despite other x/z bits; no known
one bit exits. Normal completion and `continue` reach the next test;
`break` exits without evaluating it. Nested loops consume their own transfers.
Effectful/nonintegral conditions, unresolved repeated-body lifetimes,
unsupported statements, frontend errors and symbolic-mode loops remain loud.

Ingestion maps `while` to the existing empty-initializer/empty-step `for`
control. A body-first `doWhileLoop` entry reuses that same control for
subsequent tests and iterations. Its first suspended body retains the
ordinary body boundary, so resumption completes the unfinished body before
testing. The completed-step executor correspondence includes this entry.
No scheduler, queue, synthetic signal or loop unrolling is added.

The authored values fixture matches its complete independent transcript.
Four fixture-bound kernel theorems establish false pre-test preservation,
body-first assignment, break without a post-test read, and retention of the
first event-wait boundary with arbitrary state, pending work and prior
output. A separate timer fixture matches its complete independent transcript
under both source and reverse schedule oracles.

The event fixture exposed an existing kernel integration gap: procedural
writes do not publish edges to registered waiters. The timed loader now
refuses any design whose processes may write a watched signal, including
selected/packed targets, scanner copyback and implicit clocked-process waits.
This conservative admission guard preserves the counterexample as a loud
fixture. External stimulus edges retain their existing interface. No
whole-body before/after approximation is used to invent missing intermediate
edges. See [the loop contract](sv-loops.md).

A paired **22,035**-path census gains **46 clean files** without losses:
**3,186 → 3,232 clean**, **18,783 → 18,737 partial**, **66 include skips**,
zero extraction errors. Thirty-six gains match complete time-zero transcripts
and seven more match through the timed loader under both schedule oracles.
Two remain runtime refusals because of time-zero-only `$time` lowering.
One quiescent fixture has a **diagnostic-only transcript divergence**: it
produces no user output, while the independent simulator emits a quiescence
warning. A no-loop control produces the same warning. That raw difference is
retained and is not counted as an execution match.

### Fixed-dimension foreach — 2026-10-20

IEEE 1800-2023 §12.7.3 fixed foreach loops now compile to one existing
ordinal `For`, preserving the bound dimension table as provenance. Named
indices traverse declared bounds, rightmost first; omitted dimensions do
not iterate, and an all-omitted index list executes once. The implicit
signed-int variables receive stable declaration-based storage names with
collision checks. Same-name outer variables, nested iterators and repeated
entries retain their proper scope. One loop boundary makes break exit the
whole tuple space and continue advance one tuple (§12.8).

Array reads remain live. For noncanonical packed ranges, pure signed 32-bit
indices normalize to LSB offsets after widening, preserving negative bounds
and unknown/out-of-range results (§11.5.1). Other runtime index types remain
loud: an independently run wide unsigned negative-bound probe disagrees with
mathematical offsets and is retained as an explicit refusal. Unsupported
array storage, dynamic collections, unresolved body lifetimes, invalid
compilations and symbolic-mode loops remain loud. No evaluator, scheduler or
array store changed. See [the loop contract](sv-loops.md).

Three authored acceptance sources match complete independent transcripts.
The timed source observes live four-state elements across retained bodies
under both source and reverse schedule oracles. Three kernel theorems bind
to the actual extracted tuple loop: offset evaluation, coordinate
reconstruction and whole-loop break without stepping the ordinal.

The paired **22,035**-path census gains **21 clean files** without losses:
**3,232 → 3,253 clean**, **18,737 → 18,716 partial**, **66 include skips**,
zero extraction errors. Nineteen gains match complete time-zero transcripts
and one more matches through the timed loader under both oracles. One timed
fixture remains refused by the existing time-zero-only `$time` guard.
A named-loop file stays partial because its newly visible `disable` body
remains unsupported. Extraction counts are separate from execution agreement.

### Explicit command-line plusargs — 2026-10-20

IEEE 1800-2023 §21.6 queries now carry an explicit ordered input environment
through `loadEnvelopeDesignWithPlusargs`. Ordinary loading refuses queries
without a supplied environment. Literal `$test$plusargs` preserves
case-sensitive prefix matching; integral `$value$plusargs` selects the first
match, converts the full suffix and copies back at the original statement
boundary. Absence leaves the destination untouched. Short-circuit lowering
preserves call placement and subsequent dependent reads, including unknown
left operands. Existing packed assignments handle slices and two-state
conversion; the timed stepper retains ordinary continuations. No evaluator
or scheduler changed. [The contract](sv-plusargs.md) names every remaining
format, storage, numeric-diagnostic and effect-context boundary.

The paired **22,035**-path census gains **31 clean files** without losses:
**3,253 → 3,284 clean**, **18,716 → 18,685 partial**, **66 include skips**,
zero extraction errors. Twenty-nine gains match complete independent
transcripts with each source's declared plusargs supplied to both sides.
One malformed numeric conversion remains loud after an independent diagnostic;
one timed fixture retains the existing `$time` boundary. These two are
extraction gains only. Authored time-zero and timed fixtures separately
check numeric edges, expression order and selected writes across delays.
Three kernel theorems bind first-match and copyback rules to the real fixture.

### Blocking intra-assignment timing — 2026-10-20

IEEE §10.4.1/§9.4.5 blocking controls now compile to capture, wait and
copyback using existing statements. RHS evaluation happens once at encounter;
destination selection happens after resumption. Packed concatenations,
state-kind conversion and repeated capture use existing assignment/storage
rules. Repeated events sample their count once through the existing loop
rule. No evaluator or scheduler changed. See [the contract](sv-intra-assignment.md).

The paired **22,035**-path census gains **15 clean files** without losses:
**3,284 → 3,299 clean**, **18,685 → 18,670 partial**, **66 include skips**,
zero extraction errors. Ten gains match complete independent transcripts
under both source and reverse schedule oracles. Two gains remain loud at
zero-delay Inactive delivery, and three retain the timed `$time` boundary.
Four dynamic unpacked destinations remain partial. Extraction gains are
separate from execution agreement.

Three authored acceptance sources match complete independent transcripts,
including resumed selection, X/Z neighbors, two-state concatenated copyback,
prior NBA work, repeated capture and retained event counts. Two additional
sources retain explicit zero-delay and procedural edge-publication refusals.
Three fixture-bound kernel theorems prove capture before wait, resumed-index
copyback and retained repeat control. Nonblocking controls, unsupported
effects/storage/delays and symbolic-mode controls remain loud.

### Nonblocking intra-assignment publication — 2026-10-21

The residual `IntraAssignment:publication-or-context` wall is the
nonblocking publication boundary. In the fresh 22,043-path census it is the
sole refusal in 55 files and occurs 75 times: 63 delayed controls, two event
controls, one `#0` and nine repeat/context forms. A future NBA update queue,
same-time ordering and process-lifetime rule are distinct from the blocking
capture/wait path, so no shape is admitted by serializing it or spawning a
synthetic sleeper. See [the boundary and repricing](sv-intra-assignment.md)
and the read-only instrument `extractors/sv/intra_nba_reprice.py`.

### Symmetric wildcard case statements — 2026-10-20

IEEE §12.5.1 unqualified integral `casez` and `casex` now use the existing
first-match case control chain with a shared pure symmetric match predicate.
Z is ignored in either operand; `casex` additionally ignores X. Dynamic items
and masks retain their live values, whole-case width/sign conversions precede
matching, and selected bodies retain their continuation across waits. No
scheduler changed. Effects, qualifiers, unsupported types/storage and
symbolic-mode wildcard statements remain loud. See [the contract](sv-wildcard-cases.md).

The paired **22,035**-path census gains **30 clean files** without losses:
**3,299 → 3,329 clean**, **18,670 → 18,640 partial**, **66 include skips**,
zero extraction errors. Twenty-eight gains match complete independent
transcripts under both source and reverse schedule oracles. Two delayed
corpus files retain the timed `$time` boundary and are extraction gains only.
All three authored sources match complete transcripts, covering all 256
pairs of two-bit four-state values, signed/mixed/wide contexts, dynamic masks,
first/default/no-match, nesting and retained selected arms across delays.
Three fixture-bound kernel theorems prove the evaluator bridge, symmetric
matching and selected-arm continuation.

### Forever loops — 2026-10-20

IEEE §12.7.6 `forever` retains its body and compiles to the existing loop
control with a true one-bit condition and empty initializer/step lists.
Normal completion and `continue` start the next iteration; `break` exits
only the nearest loop. Delay/event waits retain the current body tail and
loop boundary. No evaluator or scheduler changed. See [the loop contract](sv-loops.md).
Unmodelled body lifetimes, named-block `disable`, procedural edge publication,
timed clocks and symbolic-mode loops remain loud.

The paired **22,035**-path census gains **21 clean files** without losses:
**3,329 → 3,350 clean**, **18,640 → 18,619 partial**, **66 include skips**,
zero extraction errors. Ten gains match complete independent transcripts
under both source and reverse schedule oracles. Eleven gains remain runtime
refusals: seven require procedural edge publication and four retain the timed
`$time` boundary. Two additional candidates stay partial because their newly
visible bodies contain `disable`. Extraction gains are separate from runtime
agreement.

All three authored sources match complete independent transcripts, covering
nearest-loop transfers, nesting, automatic array reinitialization, termination,
live four-state values across delays and a permanently waiting event body.
Four fixture-bound kernel theorems establish event/delay retention, resumed
break and event rearming after body completion. Fuel exhaustion remains timeout.

### Case-inside membership selection — 2026-10-20

IEEE §12.5.4 unqualified integral `case … inside` now uses the existing
membership predicates and first-match case chain. Scalar labels use asymmetric
wildcard equality; colon ranges use inclusive signed/unsigned comparisons.
Only definite one selects an arm. Common-width fixed arrays/slices retain
source-order elements, and delayed selected arms retain their own continuation.
No evaluator, storage or scheduler changed. Effects, qualifiers, tolerance
syntax, unsupported types/storage, dollar case endpoints, dynamic or nested
arrays, and over-wide cells remain loud. The symbolic structural case path is
unchanged.
See [the contract](sv-case-inside.md).

The paired **22,035**-path census gains **21 clean files** without losses:
**3,350 → 3,371 clean**, **18,619 → 18,598 partial**, **66 include skips**,
zero extraction errors. All twenty-one gains match complete independent
transcripts under both source and reverse schedule oracles. Three authored
sources also match complete transcripts, including all 256 pairs of two-bit
four-state operands, type/range/array contexts and delayed live-value changes.
A fourth source now checks narrow case-array widening as a runtime match. Three
fixture-bound kernel theorems prove
the scalar equality bridge, ambiguous-item skip with retained selected body,
and inclusive signed interval guard.

### Package integral singleton storage — 2026-10-20

IEEE clause 26 source-defined packages now compile scalar/packed integral
variables into one shared vector store, before module initialization. Bound
qualified/imported/reexported references select the original slot; local
shadowing and same-named members in other packages retain distinct bindings.
Integral parameters/enumerators become exact literals; aliases use the existing
type admission. Default and closed pure initializers preserve four-/two-state
rules. Unsupported package members, dependent/effectful initialization,
unpacked/nonintegral storage, external packages, invalid source and multiple
module stores remain loud. Symbolic mode is unchanged. No scheduler changed.

The paired 22,035-path census rises 3,501 to 3,666 clean (+165), without losses.
Four authored complete transcripts match both region oracles; three further
sources retain design-level boundaries. Four source-bound kernel theorems
cover shared reads, blocking stores, captured NBA updates and commit visibility.
See [the contract](sv-package-storage.md) and
[the fixtures](../Examples/system-verilog/package_storage/README.md).

### Elaborated generate scopes and integral parameters — 2026-10-20

IEEE clauses 6, 23 and 27 now compile live unconditional/if/case generate
scopes and every elaborated loop entry to the existing module declarations
and processes. Inactive branches and zero-count loops emit no runtime work.
Original binding identity selects injective generated storage, including
repeated procedural locals, fixed arrays and delayed captures. Integral
module/local/genvar parameters become exact typed literals. Bound hierarchical
reads/stores reuse the original slots. Symbolic mode is unchanged; no scheduler
changed. Active unsupported members, cross-instance storage, dependent static
initialization, source errors and expansion limits remain loud.

The paired 22,035-path census rises 3,666 to 4,011 clean (+345), without losses.
Of the gains, **187 match complete independent transcripts under both region
oracles**. Three have legal time-zero races: one oracle matches the reference,
while reversing process order changes the output. Another 146 retain runtime
refusals (112 continuous assignments, 33 procedural edge-publication cases and
one time-zero-only clock); four have multiple top modules and remain loader
refusals. The reference compiler rejects five more sources: four constant
system-function contexts and one reset-protection pragma. None of those
refusals is counted as execution agreement. There are no other transcript
differences from both oracle traces.

Seven authored complete transcripts match both region oracles; three further
sources retain the named boundaries. Three source-bound kernel proofs certify
current reads, separation of same-named scopes and the selected branch's real
blocking assignment. See [the contract](sv-elaborated-generate.md) and
[the fixtures](../Examples/system-verilog/elaborated_generate/README.md).


### Integral assignment patterns — 2026-10-20

IEEE §10.9 positional, member/index/type/default and constant-replicated
patterns now compile to existing integral concatenation and storage rules.
Bound element correspondence retains widths, sign and X/Z; keyed numeric-index
inventories map to declared order in packed values and existing unpacked-cell
paths. Nested structs, typed conditional operands, live reads, whole-packed
self-swaps, two-state conversion and NBA capture use the existing evaluator
and scheduler. Effects, invalid source, unsupported types/storage, split-cell
self-aliases and expansion limits remain loud. Symbolic packed-pattern
admission is unchanged.

The paired 22,035-path census rises 4,011 to 4,037 clean (+26), without losses.
Twenty-four gains match complete independent transcripts under both region
oracles; two retain continuous-assignment runtime refusals. All 26 independent
runs succeed, with no other differences or absent observations. All 69
previously clean pattern-bearing sources retain identical extracted designs.
Five authored transcripts match both oracles; three more preserve boundaries.
Four source-bound kernel proofs certify current reads, blocking stores, NBA
capture and commit visibility after the source changes. See
[the contract](sv-assignment-patterns.md) and
[the fixtures](../Examples/system-verilog/assignment_patterns/README.md).


### Integral replication — 2026-10-20

IEEE §11.4.12.1 pure integral replication lowers whole self-determined groups
to the existing concatenation rule. Source order, nested groups, X/Z,
byte-string literals, parameter counts, unsigned results and later assignment
resizing are retained. Legal zero-count members contribute no bits while
still checking their source. Effects, unsupported types/operands, invalid
compilations and bounded expansions stay loud. Symbolic extraction is
unchanged; no evaluator, storage primitive or scheduler is added.

Independent comparison exposed and corrected §5.7.1 wide unsized based X/Z
context fill. Sized literals and unsigned values still zero-fill. Affected
frontend parameter/enum/generate constants and constant selectors refuse
rather than use an incorrect elaboration result.

The paired 22,035-path census rises 4,037 to 4,057 clean (+20), without losses.
All 20 gains execute completely and match independent transcripts under both
region oracles. All 4,037 previously clean designs extract identically.
Seven authored sources match both oracles; three preserve effect,
dynamic-string and elaboration-constant refusals. Five kernel proofs certify
the actual parsed live RHS, blocking store, NBA capture, post-change visibility
and zero-member identity. See [the contract](sv-replication.md) and
[the fixtures](../Examples/system-verilog/replication/README.md).


### Runtime integral `$clog2` — 2026-10-20

IEEE §20.8.1 pure integral calls now evaluate live finite-width operands as
unsigned bits and reuse the existing `Param.lean` ceiling-log2 definition.
Zero/one, powers/neighbors, signed operands and arbitrary supported vector
widths return a signed 32-bit integer; assignment converts afterward. Nested
calls and existing loops/cases/patterns/replication/cells compose. Correct
constant literals and symbolic extraction stay unchanged. No scheduler or
storage primitive is added.

Runtime X/Z, effects and unsupported types stay loud. Enclosing folds and
zero replication cannot erase an unresolved numeric call; affected frontend
parameter/enum/generate constants and selectors refuse rather than use an
approximation. Independent tools disagree on unknown arguments, so no numeric
conformance claim is made for them. Unevaluated `$bits` stays a type query.

The paired 22,035-path census rises 4,057→4,070 clean (+13), without losses.
All 13 gains execute completely and match independent transcripts under both
region oracles; all 4,057 previously clean extracted designs remain identical.
Four authored sources match both oracles, with four further deliberate
refusals. Five source-bound kernel proofs cover current reads, blocking
storage, captured NBA values, post-change visibility and unknown refusal.
See [the contract](sv-runtime-clog2.md) and
[the fixtures](../Examples/system-verilog/runtime_clog2/README.md).


### Selected compound assignments — 2026-10-20

IEEE §10.4.1/§11.4.1 blocking operator assignments now cover admitted packed
selections, members and fixed unpacked cells. The extractor substitutes a
current-value read into the frontend's complete bound RMW tree, preserving
context widths/signs and final conversions. Dynamic addresses are captured
once; dynamic arrays capture their computed result before cell copyback and
filter unrepresentable labels. Bounded member temporaries protect adjacent
fields. Existing local/store/continuation/NBA rules remain the authority.

`CompoundRead` adds one expression admission check: an overlapping partial
packed range refuses after two measured reference disagreements. The exact
sources and observations remain as refusal fixtures. Wholly invalid and X
selectors retain no-store behavior while still evaluating the RHS. Source
effects, unsupported lvalues/types, internal timing and symbolic compounds
remain loud; externally delayed statements compose normally.

The paired 22,035-path census gains 13 clean designs, with no losses:
4,083 clean/17,886 partial/66 include skips/zero errors. All 13 gains match
complete reference transcripts under both oracles; all 4,070 previously clean
extracted designs remain identical. Seven authored complete matches and four
refusals accompany five kernel theorems bound to the real parsed delayed
assignment. See [the contract](sv-compound-assignments.md) and
[the receipts](../Examples/system-verilog/compound_assignments/README.md).

### Min typ max expressions — 2026-10-20

IEEE §11.11/§10.8 legacy extraction now chooses min/typ/max globally at
elaboration, default typical, with explicit `--min-typ-max` and recorded
nondefault metadata. The complete selected bound expression retains width,
signedness and conversions, and only that arm executes or enters purity/
numeric/alias analyses. Frontend validity still covers the whole compilation.
The loader checks the wrapper and parses its selected operand directly;
existing evaluators, blocking/NBA stores and literal-delay timers apply.
Selected effects/types/calls, dynamic delays, frontend-invalid forms and
nonconstant symbolic choices remain loud. Existing symbolic constant folding
is unchanged. No scheduler change is involved.

The paired 22,035 paths gain 15 clean files, no losses: 4,098 clean, 17,871
partial, 66 include skips, zero errors. Fourteen gains match complete reference
transcripts under both region oracles; one retains the existing timed `$time`
refusal. One of 4,083 previously clean envelopes expands a constant into the
selected tree; both versions match the same reference. Thirty authored mode/
source pairs give 20 complete matches and 10 explicit refusals. Five kernel
theorems bind the parsed live RHS and blocking/NBA statements. The exact
reference-accepted direct-display-argument frontend refusal is retained.
See [the contract](sv-min-typ-max.md) and
[the fixtures](../Examples/system-verilog/min_typ_max/README.md).

### Static portless module hierarchy — 2026-10-20

IEEE clauses 23/27 legacy elaboration now traverses actual concrete module
bodies, including generated/static-array instances and parameter overrides.
All supported declarations are bound before expression conversion; distinct
instance storage and procedural locals retain length-prefixed structural
routes even when their frontend canonical body is shared. Parent/child/
sibling/upward references name their original declaration. Package storage
is shared once. Existing execution, continuations, NBA work and region oracles
apply. No scheduler change is involved.

Child ports, interface/program kinds, differing timescales, over-budget
expansion, invalid/redefined source, new static-initializer order dependence
and unsupported active members stay loud. Symbolic mode is unchanged. This
is the first hierarchy rung, not connected-port or full hierarchy coverage.
The paired 22,035 paths gain 198 clean files, no losses: 4,296 clean, 17,673
partial, 66 include skips, zero errors. All 4,098 previous clean designs remain
identical. Five kernel theorems bind actual parsed cross-instance storage and
blocking/NBA statements.

Of the 198 gains, 175 match complete independent transcripts under both
region oracles; nine match one tested legal order. Those nine contain
same-tick output ordering, early `$finish`, or an initial-write race; their
other traces are retained rather than counted as both-order matches. Eleven
retain runtime refusals: three continuous assignments, two procedural-edge
publication cases, two timed `$time` cases, two designs without procedural
processes, one zero-delay Inactive delivery and one run without `$finish`.
Two nested-module sources hit reference-compiler limitations, and one
multiple-top source has no usable single-top oracle. No successful reference
transcript falls outside both tested model traces. Eight authored/prior
fixtures match both orders; four explicit boundary fixtures remain refusals.
Final-source authentication covers 207 successful independent invocations
and two compiler refusals. Five kernel theorems certify the parsed
cross-instance storage and blocking/NBA statements.

See [the contract](sv-module-hierarchy.md) and
[the fixtures](../Examples/system-verilog/module_hierarchy/README.md).

### Connected child ports — 2026-10-21

The hierarchy repricing pass measures the residual `Hierarchy:ports` wall at
the frontend's concrete child-instance boundary. In the fresh 22,043-path
census it occurs in 2,397 files: 1,186 port-only and 1,211 co-occurring. Those
port-only files contain 1,481 child instances with declared ports; 1,423 are
fully connected, 43 have at least one omitted connection, and 15 are wholly
unconnected. Connected inputs/outputs need assignment-like conversion plus
continuous propagation, while `inout` needs bidirectional aliasing and
resolution. Omitted inputs retain `z`/default rules. The flat store has none
of those representations, so no safe connected-port subfamily is admitted;
child ports remain loud and the static hierarchy rung stays portless. See
[the boundary and repricing](sv-hierarchy-ports.md) and the read-only
instrument `extractors/sv/hierarchy_reprice.py`.

### Program and interface hierarchy — 2026-10-21

The next hierarchy repricing pass measures the residual
`Hierarchy:module-kind` wall. In the fresh 22,043-path census it occurs in
1,248 files: 319 module-kind-only and 929 co-occurring. Those sole files
contain 365 concrete non-module instances: 330 programs and 35 interfaces.
There are 57 top-level programs, 273 nested programs, and 35 nested
interfaces; 279 instances are portless and 86 have ports. Programs require
reactive-region, completion, final and `$exit` behavior. Interfaces require
design-signal, modport, clocking and binding behavior. The module executor
cannot represent either by flattening it as an ordinary module, so all
program/interface instances remain loud and no second scheduler is added. See
[the boundary and repricing](sv-hierarchy-kinds.md) and the read-only
instrument `extractors/sv/hierarchy_kind_reprice.py`.

### Subroutines — 2026-10-21

The next refusal repricing measures `SubroutineSymbol:Subroutine`. In the
fresh 22,043-path census it occurs in 1,714 files: 108 subroutine-only and
1,606 co-occurring. Those sole files contain 126 unsupported declaration
instances: 70 functions, 23 tasks and 33 DPI imports. Functions need formal
conversion, return context, locals, recursion and effects; tasks add blocking,
retained continuations and output/ref/inout copyback; DPI imports require an
external ABI and oracle. Constant-function candidates still need a separate
elaboration evaluator and legality boundary. No declaration shape is
independently admissible by dropping its body or treating a call as pure. See
[the boundary and repricing](sv-subroutines.md) and the read-only instrument
`extractors/sv/subroutine_reprice.py`.

### Primitive instances — 2026-10-21

Structural primitive repricing is the next largest sole boundary:
`PrimitiveInstanceSymbol:PrimitiveInstance` occurs in 1,153 files, with 583
primitive-only and 570 co-occurring after primitive-array extraction was made
explicit. The sole files contain 811 concrete instances: 392 logic gates, 121
conditional gates, 146 MOS switches, 78 tran switches and 74 pull sources.
One hundred twenty have delays and 691 do not. Even a no-delay gate needs
continuous publication, four-state net resolution and driver state; switches
and pull sources add bidirectionality and strength. The current scalar/packed
store has no driver graph, so every primitive family remains loud until it can
call the existing scheduler with a real driver representation. See [the
boundary and repricing](sv-primitives.md) and the read-only instrument
`extractors/sv/primitive_reprice.py`.

### `trireg` charge-storage nets — 2026-10-22

`NetSymbol:TriReg` remains the capacitive-net boundary. The fresh 22,043-path
census records it in 53 files: 17 are `TriReg`-only and 36 co-occur with
another wall. The sole files contain 21 concrete declarations, including 11
explicit charge-strength declarations, 14 driver-release forms, nine retained
charge observations, four four-state `x` cases, two undriven-startup cases,
two capacitive-network declarations, one charge-decay delay and one signed
packed vector (features overlap). A `trireg` needs driver identity, resolved
four-state publication, charge strength, capacitive retention and optional
decay scheduling. The envelope has no such state, so no declaration is
treated as an ordinary wire or variable and no second scheduler is added. See
[the boundary and repricing](sv-trireg.md) and the read-only instrument
`extractors/sv/trireg_reprice.py`.

### `tri0` implicit pull nets — 2026-10-22

`NetSymbol:Tri0` remains the implicit-driver boundary. The fresh 22,043-path
census records it in 22 files: 11 are `Tri0`-only and 11 co-occur with
another wall. The sole files contain 11 declarations: all have an implicit
pull-0, eight observe an undriven net, three have a continuous driver, one
uses explicit driver strength, one tests a strong-driver override and one
tests an `x` driver (features overlap). The envelope has no implicit pull
driver, strength ordering or resolved four-state driver set, so no `tri0` is
reduced to a constant or ordinary wire and no second scheduler is added. See
[the boundary and repricing](sv-tri0.md) and the read-only instrument
`extractors/sv/net_pull_reprice.py`.

### `tri1` implicit pull nets — 2026-10-22

`NetSymbol:Tri1` remains the implicit-driver boundary. The fresh 22,043-path
census records it in 20 files: 10 are `Tri1`-only and 10 co-occur with
another wall. The sole files contain 10 declarations: all have an implicit
pull-1, six observe an undriven net, four have a continuous driver, three test
a strong-driver override, one tests a release and one tests an `x` driver
(features overlap). The envelope has no implicit pull driver, strength
ordering or resolved four-state driver set, so no `tri1` is reduced to a
constant or ordinary wire and no second scheduler is added. See [the boundary
and repricing](sv-tri1.md) and the read-only instrument
`extractors/sv/tri1_reprice.py`.

### `tri` resolved nets — 2026-10-22

`NetSymbol:Tri` remains the resolved-wire boundary. The fresh 22,043-path
census records it in 66 files: 7 are `Tri`-only and 59 co-occur with another
wall. The sole files contain 7 declarations: three continuous single-driver
forms, four undriven observations, two wire/tri equivalence comparisons, two
invalid `tri reg` spellings and one floating four-state observation (features
overlap). The envelope has no general driver set or strength-resolution state,
so no `tri` is renamed to `wire` and no invalid declaration is salvaged. See
[the boundary and repricing](sv-tri.md) and the read-only instrument
`extractors/sv/tri_reprice.py`.

### `interconnect` hierarchical nets — 2026-10-22

`NetSymbol:Interconnect` remains the hierarchical-connectivity boundary. The
fresh 22,043-path census records it in 15 files: 8 are Interconnect-only and
7 co-occur with another wall. The sole files contain 10 declarations: three
initializers, two delay specifications, one min:typ:max delay, one explicit
data type, one drive/charge strength, two packed dimensions, two unpacked
dimensions and one per-bit net-type resolution observation (features
overlap); six are compile-error diagnostic shapes. The envelope has no
elaborated port graph, bidirectional connection identity or per-bit net-type
resolution, so no interconnect is rewritten as a local wire and no invalid
declaration is salvaged. See [the boundary and repricing](sv-interconnect.md)
and the read-only instrument `extractors/sv/interconnect_reprice.py`.

### Concurrent assertions — 2026-10-21

Concurrent assertion repricing measures `ConcurrentAssertionStatement` in
1,358 files: 539 assertion-only and 819 co-occurring. The sole files contain
639 statements: 562 `assert property`, 37 `cover property`, nine `assume
property`, eight `cover sequence`, 21 `expect` and two `restrict` forms.
These statements sample in Preponed, retain sequence attempts across ticks,
evaluate in Observed and publish actions through Reactive/coverage regions.
Their flavors are not immediate booleans, so no form is admitted by the
existing assertion action path and no second scheduler is added. See [the
boundary and repricing](sv-concurrent-assertions.md) and the read-only
instrument `extractors/sv/concurrent_assert_reprice.py`.

### Property declarations — 2026-10-21

`PropertySymbol:Property` is the named concurrent-property declaration
boundary, separate from assertion statements that use a property. In the
fresh 22,043-path census it occurs in 471 files: 10 are property-only and 461
co-occur with another wall. The sole files contain 11 unsupported property
spans, including six clocked, four implication, three formal-argument, two
local-variable, two sampled-function, one abort/disable and one end-label
feature rows (rows overlap). Formal arguments, sampled history and
sequence-attempt state have no representation in the module envelope, so no
declaration shape is admitted by inlining or boolean evaluation. See [the
property boundary](sv-properties.md) and the read-only instrument
`extractors/sv/property_reprice.py`.

### Covergroup declarations — 2026-10-21

`CovergroupType:CovergroupType` is the verification-object declaration
boundary. In the fresh 22,043-path census it occurs in 725 files: eight are
covergroup-only and 717 co-occur with another wall. The sole files contain
nine unsupported covergroup spans, including nine coverpoints, six bin
declarations, three clocked samples, three sample-argument directions, two
options, two sample methods, one `with` expression and one cross (rows
overlap). The envelope has no sampling event, bin database or cross state, so
no covergroup shape is admitted by flattening it into module storage. See
[the covergroup boundary](sv-covergroups.md) and the read-only instrument
`extractors/sv/covergroup_reprice.py`.

### Compilation-unit covergroups — 2026-10-21

The separate `CovergroupType` marker covers compilation-unit covergroup
declarations. In the fresh 22,043-path census it occurs in five files: three
are covergroup-only and two co-occur with another wall. The sole files contain
six spans, with three clocked, three `extends`, four coverpoint and two bin
feature rows (overlapping). Top-level inheritance remains a diagnostic and
coverage-object boundary; no declaration is moved into an artificial module.
See [the covergroup boundary](sv-covergroups.md) and the read-only instrument
`extractors/sv/top_covergroup_reprice.py`.

### Parameterized class declarations — 2026-10-21

`GenericClassDefSymbol` is the value/type-parameterized class boundary. In the
fresh 22,043-path census it occurs in 146 files: 10 are generic-class-only and
136 co-occur with another wall. The sole files contain 10 spans, including
nine value-parameter, five type-parameter, eight virtual-class, seven
typedef-member, two static-method, two packed-aggregate-type and one
local-parameter feature rows (overlapping). The envelope has no
specialization table or parameter environment, so no generic class is reduced
to a default specialization. See [the generic-class boundary](sv-generic-classes.md)
and the read-only instrument `extractors/sv/generic_class_reprice.py`.

### Generic class member and scope uses — 2026-10-21

`GenericClassDefSymbol:GenericClassDef` is the separate parameterized-class
member/scope boundary. In the fresh 22,043-path census it occurs in 39 files:
two are generic-class-use-only and 37 co-occur with another wall. The sole
files contain two spans, with one value-parameter member, one type-parameter
member, one local-parameter member and one class-scope resolution row
(overlapping). The envelope does not perform member parameter iteration or
type-scope lookup as a specialization shortcut. See [the generic-class
boundary](sv-generic-classes.md) and the read-only instrument
`extractors/sv/generic_class_use_reprice.py`.

### Type parameters — 2026-10-21

`TypeParameterSymbol:TypeParameter` is the type-binding boundary. In the fresh
22,043-path census it occurs in 18 files: eight are type-parameter-only and
10 co-occur with another wall. The sole files contain nine spans, including
three empty frontend spans, four `type(...)` operator spans and two
typed-default spans (overlapping). The envelope has no type environment or
type-operator node, so no override or dependent declaration is reduced to a
default type. See [the type-parameter boundary](sv-type-parameters.md) and
the read-only instrument `extractors/sv/type_parameter_reprice.py`.

### Final procedures — 2026-10-21

`ProceduralBlockSymbol:Final` is the end-of-simulation shutdown boundary. In
the fresh 22,043-path census it occurs in 88 files: 39 are final-only and 49
co-occur with another wall. The sole files contain 45 final spans, including
39 block bodies, 33 assignments or increments, 38 `$display` calls, four
`$finish` calls, two assertion/`$fatal` sites, three delays, one `wait` and one
`$time` query (features overlap). A final procedure runs once when simulation
ends, after the finish condition, in a function-like shutdown context with
its own completion and ordering rules. It cannot be treated as `initial`, a
delayed process or an independent concurrent process. The envelope has no
end-of-simulation queue or final invocation frame, so no final body is
admitted by running it at time zero or adding a second scheduler. See [the
final boundary](sv-final.md) and the read-only instrument
`extractors/sv/final_reprice.py`.

### Implicit event controls — 2026-10-22

`TimedStatement:ImplicitEventControl` is the inferred-sensitivity boundary
for `@*` and `@(*)`. In the fresh 22,043-path census it occurs in 53 files:
38 are implicit-control-only and 15 co-occur with another wall. The sole files
contain 38 spans: 29 bare `@*`, nine `@(*)`, 25 block bodies, 14 case
statements, five indexed selects, four conditionals, three nested controls,
three concatenations and one system call (features overlap). IEEE sensitivity
inference reads branches, case items, indexes and concatenations while
excluding identifiers used only in nested timing controls. The envelope has
no inferred read-set or rearming state, so no implicit event control is
admitted by guessing a list, running it once or adding a scheduler. See [the
implicit-event boundary](sv-implicit-events.md) and the read-only instrument
`extractors/sv/implicit_event_reprice.py`.

### Unique case statements — 2026-10-22

`CaseStatement:Unique` is the first-match plus diagnostic boundary. In the
fresh 22,043-path census it occurs in 45 files: 37 are unique-case-only and
eight co-occur with another wall. The sole files contain 38 spans, including
20 `default` arms in 19 files, nine nonblocking updates, five indexed selects,
four multi-label items, four `casez`, one `casex`, one `inside` case and one nested
block (features overlap). A unique case must retain ordinary first-match
selection while reporting zero- or multi-match violations; the envelope has
no diagnostic channel or retained case-check state. No qualifier is erased,
no fixed arm is selected, and no second scheduler is introduced. See [the
unique-case boundary](sv-unique-cases.md) and the read-only instrument
`extractors/sv/unique_case_reprice.py`.

### Unique-if statements — 2026-10-22

`ConditionalStatement:Unique` remains the first-match plus all-condition
diagnostic boundary. The fresh 22,044-path census records it in **20** files:
**16** are unique-if-only and **4** co-occur with another wall. Repricing the
sole files finds **16** spans: **10** no-match paths without a final `else`,
**6** explicit `else` fallbacks, **4** potentially multiple-true chains,
**3** `always_comb` contexts, **2** reschedule-flush rows, one nested chain,
one `always` context, one Observed-region report, one event-resume flush, one
loop context and one invalid qualifier after `else` (features overlap).

The ordinary `If` envelope has no uniqueness status or diagnostic channel,
all-condition evaluation record, or pending-report state tied to a retained
process. No qualifier is erased, no fixed arm is chosen, and no scheduler is
added. See [the unique-if boundary](sv-unique-if.md) and the read-only
instrument `extractors/sv/unique_if_reprice.py`.

### Priority case statements — 2026-10-22

`CaseStatement:Priority` remains the first-match plus no-match diagnostic
boundary. The fresh 22,044-path census records it in **12** files, all
priority-case-only. Repricing finds **13** spans: **6** without a `default`,
**7** with one, **5** indexed selects, **4** `casez`, **6** wildcard labels,
**3** `inside` cases, **4** multi-label items, **2** `always_comb` contexts
and one explicit no-match violation row (features overlap). The ordinary case chain lacks priority status and a no-match
diagnostic channel, so no qualifier is erased and no arm is selected. See
[the priority-case boundary](sv-priority-cases.md) and the read-only
instrument `extractors/sv/priority_case_reprice.py`.

### Priority-if statements — 2026-10-22

`ConditionalStatement:Priority` remains the listed-order first-match plus
no-match diagnostic boundary. The fresh 22,044-path census records it in **9**
files, all priority-if-only. Repricing finds **9** spans: **6** explicit
`else` fallbacks, **2** no-match paths without a final `else`, **4**
potentially multiple-true chains, **2** indexed selects, **2** `always_comb`
contexts, one explicit no-match violation and one invalid qualifier after
`else` (features overlap). The ordinary conditional chain lacks priority
status and a no-match diagnostic channel, so no qualifier is erased and no
branch is selected. See [the priority-if boundary](sv-priority-if.md) and the
read-only instrument `extractors/sv/priority_if_reprice.py`.

### Unique0 case statements — 2026-10-22

`CaseStatement:Unique0` remains the first-match plus multiple-match
diagnostic boundary with an explicitly allowed no-match. The fresh 22,044-path
census records it in **8** files, all unique0-case-only. Repricing finds **10**
spans: **10** no-match-allowed paths without a `default`, **9** no-match
rows without violation, **3** `casex`, **4** wildcard labels, **2** indexed
selects, **2** `inside` cases, one `casez` and one multiple-match violation
row (features overlap). The
ordinary case chain has no overlap status, so no qualifier is erased, no arm
is selected and no no-match behavior is invented. See [the unique0-case
boundary](sv-unique0-cases.md) and the read-only instrument
`extractors/sv/unique0_case_reprice.py`.

### Randcase statements — 2026-10-22

`RandCaseStatement` is the weighted-random branch boundary. In the fresh
22,043-path census it occurs in 35 files: 31 are randcase-only and four
co-occur with another wall. The sole files contain 33 spans, including three
all-zero-weight cases, 12 zero-weight branches, ten expression-weight spans,
seven indexed targets, 21 increments and one branch block (features overlap).
IEEE §12.10/§18.16 samples each weight for the execution and excludes zero
weights; the envelope has no random oracle, sampled weight vector or selection
trace. No branch is selected by a fixed seed or source order, and no second
scheduler is introduced. See [the randcase boundary](sv-randcase.md) and the
read-only instrument `extractors/sv/randcase_reprice.py`.

### Disable statements — 2026-10-22

`DisableStatement` is the named-scope cancellation boundary. In the fresh
22,043-path census it occurs in 45 files: 28 are disable-only and 17 co-occur
with another wall. The sole files contain 28 spans, including 25 named
targets, two escaped targets and one statement label. IEEE §9.6.2 and §12.6
terminate the selected named block or label, skip its remaining statements and
resume after that scope; named forks and blocks can cancel retained child
activity. The envelope has no target-scope identity, cancellation token or
retained continuation tree. No target is guessed, no disable is lowered to
`break`, return or silent child cancellation, and no second scheduler is
introduced. See [the disable boundary](sv-disable.md) and the read-only
instrument `extractors/sv/disable_reprice.py`.

### Specify blocks — 2026-10-22

`SpecifyBlockSymbol:SpecifyBlock` is the structural timing-model boundary. In
the fresh 22,043-path census it occurs in 54 files: 28 are specify-only and 26
co-occur with another wall. The sole files contain 28 spans, including 14
timing checks, 12 module paths, 14 edge-sensitive forms, ten scalar delays,
seven notifier references, five state-dependent paths, four indexed terminals,
three conditional paths, three polarity forms, two tuple delays, one `ifnone`
path, one illegal edge specification, one invalid concurrent assertion and one
invalid system task (features overlap). IEEE §§30–32 give these declarations
path-delay, timing-check, pulse and diagnostic semantics. The envelope has no
path-delay graph, timing-check monitor, pulse state or notifier publication.
No specify declaration is dropped or run as a procedural block, and no second
scheduler is introduced. See [the specify boundary](sv-specify.md) and the
read-only instrument `extractors/sv/specify_reprice.py`.

### Net aliases — 2026-10-22

`NetAliasSymbol:NetAlias` is the bidirectional net-topology boundary. In the
fresh 22,043-path census it occurs in 35 files: 25 are alias-only and ten
co-occur with another wall. The sole files contain 31 spans, including 11
indexed-select spans in seven files, four chained aliases, 12 declarations in
six files with multiple alias statements, four alias spans in three generated
placements and one protected-region span (features overlap). IEEE §§6.7.2 and
10.11 make aliases an elaboration-time relationship among nets; drivers and
resolved values remain visible through every name. The envelope has no alias
graph or resolved-driver topology. No alias is erased, made one-way or
replaced by an initial assignment, and no second elaborator or scheduler is
introduced. See [the net-alias boundary](sv-net-alias.md) and the read-only
instrument `extractors/sv/net_alias_reprice.py`.

### Package initializers — 2026-10-22

`Package:initializer` is the package initialization-order boundary. In the
fresh 22,043-path census it occurs in 41 files: 25 are initializer-only and 16
co-occur with another wall. The sole files contain 35 spans, all with a runtime
variable reference; 14 use arithmetic in 11 files, six contain multiple
referenced identifiers, one uses a qualified package reference, and 19 occur
in nine files with multiple initializers (features overlap). Export contexts
occur in 24 spans across 17 files, including nine wildcard-export spans in
five files. IEEE §26.2 runs package initializers before any process starts and
in declaration order. The envelope has no dependency graph or initialization
phase for these reads. No initializer is folded to a constant, dropped or run
as a module process, and no second scheduler is introduced. See [the
package-initializer boundary](sv-package-initializers.md) and the read-only
instrument `extractors/sv/package_initializer_reprice.py`.

### Event lists — 2026-10-22

`TimedStatement:EventListControl` is the multi-event wait boundary. In the
fresh 22,043-path census it occurs in 38 files: 24 are event-list-only and 14
co-occur with another wall. The sole files contain 25 spans, including 21 `or`
lists, six comma lists, ten edge events, four `iff` filters, three lists with
at least three events, four block bodies, three `always_ff` controls, one
parenthesized list, one indexed expression and one procedural assign/deassign
(features overlap). IEEE §§9.4.2, 12.4 and 12.6 wake a process on any listed
event, apply edge and adjacent `iff` filters at occurrence time, and re-arm the
same continuation. The envelope has no multi-event registration, per-event
guard or retained rearming state. No list is reduced to one signal or a fixed
sequence, and no second scheduler is introduced. See [the event-list boundary](sv-event-lists.md)
and the read-only instrument `extractors/sv/event_list_reprice.py`.

### Clocking blocks — 2026-10-22

`ClockingBlockSymbol:ClockingBlock` is the scheduler-region synchronization
boundary. In the fresh 22,043-path census it occurs in 562 files: 24 are
clocking-only and 538 co-occur with another wall. The sole files contain 24
spans, including eight global declarations, four default declarations, eight
input clockvar forms, five output clockvar forms, four sequence/property-
containing blocks, five nested event/control forms (including one nested
clocking block), three generated placements, one skew declaration, one
end-label and one unnamed clocking block (features overlap). IEEE §14 samples
input clockvars and schedules output drives around the clocking event with
skew; global/default declarations also affect assertion and sequence scope. The
envelope has no clockvar sample/drive queues, skew representation or region
bridge. No block is reduced to an ordinary event wait, and no second scheduler
is introduced. See [the clocking-block boundary](sv-clocking-blocks.md) and
the read-only instrument `extractors/sv/clocking_reprice.py`.

### Invalid package compilations — 2026-10-22

`Package:invalid-compilation` is the package diagnostic boundary. In the fresh
22,043-path census it occurs in 146 files: 24 are invalid-package-only and 122
co-occur with another wall. The sole files contain 24 diagnostic spans,
including three repeated-timeunit declarations, 19 import cases, ten files
with multiple imports, nine wildcard imports, eight export cases, six combined
import/export cases, one `export *::*` case and two exports without a
corresponding import (features overlap). IEEE §26 requires these declarations
to pass scope and consistency checks before elaboration. The envelope has no
diagnostic provenance, package scope graph or partial-elaboration contract.
No package is salvaged or reduced to its first import, and no recovery
elaborator or second scheduler is introduced. See [the invalid-package
boundary](sv-package-invalid.md) and the read-only instrument
`extractors/sv/package_invalid_reprice.py`.

### Procedural continuous assignments and force/release — 2026-10-22

`ProceduralAssignStatement` is the retained-driver boundary. In the fresh
22,043-path census it occurs in 112 files: 23 are procedural-assign-only and
89 co-occur with another wall. The sole files contain 27 spans: 16 `assign`
forms and 11 `force` forms, including nonliteral RHS expressions, explicit
reevaluation scenarios, force/assign priority, replacement of an active
assignment, mixed-assignment diagnostics, net and variable targets,
concatenation and part-select LHS forms, an event-triggered process and two
chapter-37 statement forms (features overlap). IEEE §§4.9.2, 10.6.1 and
10.6.2 require retained procedural drivers, source sensitivity, force priority
and release restoration. The envelope has no such driver or resolution state,
so `assign`, `deassign`, `force` and `release` remain loud; no second
scheduler is introduced. See [the procedural assign boundary](sv-procedural-assign.md)
and the read-only instrument
`extractors/sv/procedural_assign_reprice.py`.

### Defparam overrides — 2026-10-22

`DefParamSymbol:DefParam` is the hierarchy-elaboration override boundary. In
the fresh 22,043-path census it occurs in 49 files: 23 are defparam-only and
26 co-occur with another wall. The sole files contain 33 spans, all with
hierarchical targets; they include deep and instance-array paths, source-order
last-wins updates, multi-target statements, parameter-valued RHS expressions,
instance-override precedence, generate-order dependence, invalid cross-array
targets, a dependent-parameter chain and a chapter-37 type form (features
overlap). IEEE §§6.20, 23.10 and 23.10.4 require hierarchy resolution,
override precedence and parameter-before-generate ordering. The envelope has
no such elaboration state, so no defparam is rewritten as a local constant or
inline instance override and no second elaborator or scheduler is introduced.
See [the defparam boundary](sv-defparam.md) and the read-only instrument
`extractors/sv/defparam_reprice.py`.

### Net delays — 2026-10-22

`NetSymbol:delay` is the delayed-net publication boundary. In the fresh
22,043-path census it occurs in 27 files: 21 are net-delay-only and six
co-occur with another wall. The sole files contain 22 spans, including
declaration-time continuous-assignment delays, rise/fall and turn-off values,
min:typ:max tuples, vector-wide delays, four-state transitions, inertial
cancellation/rescheduling, net-versus-assignment placement and two chapter-37
type forms (features overlap). IEEE §§10.3.3, 4.9.1 and 28.16 require delayed
driver publication and transition-dependent selection. The envelope has no
transition queue or inertial state, so no net delay is erased or replaced by
an immediate assignment and no second scheduler is introduced. See [the net
delay boundary](sv-net-delays.md) and the read-only instrument
`extractors/sv/net_delay_reprice.py`.

### Continuous-assignment delays — 2026-10-22

`ContinuousAssignSymbol:delay` is the delayed continuous-driver boundary. In
the fresh 22,043-path census it occurs in 21 files: 13 are
continuous-assignment-delay-only and eight co-occur with another wall. The
sole files contain 13 spans, including rise/fall and three-delay forms,
vector outputs, inertial cancellation/rescheduling, four-state `z`
transitions, initial-X settling, strength-before-delay ordering and a
chapter-37 type form (features overlap). IEEE §§10.3, 10.3.3 and 4.9.1
require a retained delayed driver and transition-dependent publication. The
envelope has no delayed-driver queue or inertial state, so no delayed assign
is rewritten as an immediate assignment and no second scheduler is
introduced. See [the continuous-assignment delay boundary](sv-continuous-assign-delays.md)
and the read-only instrument
`extractors/sv/continuous_assign_delay_reprice.py`.

### Dynamic delay expressions — 2026-10-22

`TimedStatement:DelayControl:expression` is the runtime delay-expression
boundary. In the fresh 22,043-path census it occurs in 168 files: 20 are
delay-expression-only and 148 co-occur with another wall. The sole files
contain 24 spans, including dynamic parameter/signal references, fixed-point
and unit-suffixed time literals, timeunit/timeprecision rounding contexts,
X/Z-to-zero behavior, delayed assignments, arithmetic expressions and
time-query contexts (features overlap). IEEE §§9.4.1, 5.8, 3.14.2.3 and 22.4
require encounter-time sampling and time-scale conversion. The envelope has
only a fixed integral delay form, so no dynamic expression is folded to a
guessed constant and no second time wheel is introduced. See [the dynamic
delay-expression boundary](sv-delay-expressions.md) and the read-only
instrument `extractors/sv/delay_expression_reprice.py`.

### Event controls over expressions — 2026-10-22

`SignalEventControl:clock` is the expression-sampling event boundary. In the
fresh 22,035-path census it occurs in 350 files: 20 are event-expression-only
and 330 co-occur with another wall. The sole files contain 20 spans, including
four multibit edge controls whose least-significant bit affects the edge,
16 value-change controls, three binary expressions, one concatenation, one
conditional, three reductions or unary expressions, three selected
expressions, four singular/aggregate cases, 11 result-change scenarios and
one scheduler-context row (features overlap). IEEE §9.4.2 samples the complete
expression, retains its prior result and applies four-state edge conversion
before re-arming the same continuation. The envelope has no expression
sampler, dependency set or retained result, so no expression is reduced to one
operand or a fixed bit and no second scheduler is introduced. See [the event
expression boundary](sv-event-expressions.md) and the read-only instrument
`extractors/sv/event_expression_reprice.py`.

### Level-sensitive wait statements — 2026-10-22

`WaitStatement` is the level-sensitive condition boundary. In the fresh
22,035-path census it occurs in 65 files: 18 are wait-only and 47 co-occur
with another wall. The sole files contain 18 spans, including six already-true
or no-block cases, three negated conditions, three four-state producer values,
two trailing-delay releases, one conjunction, one disjunction, one case
equality, one same-time NBA condition and one while-loop recheck (features
overlap). IEEE §§9.4.3 and 12.6.3 sample the condition at entry and retain the
continuation while a false condition is re-evaluated after relevant updates.
The envelope has no level-wait sampler or dependency registration, so no wait
is reduced to an edge control or executed immediately and no second scheduler
is introduced. See [the wait-statement boundary](sv-wait-statements.md) and
the read-only instrument `extractors/sv/wait_reprice.py`.

### Invalid statement markers — 2026-10-21

`InvalidStatement` is a frontend recovery marker rather than an IEEE
statement family. It occurs in 1,329 files: 606 marker-only and 723
co-occurring. The sole files contain 568 bad `begin`/block recovery spans, 31
VPI system-task tokens and seven empty frontend spans. A bad block can contain
valid-looking assignments and delays around an unsupported VPI call or
malformed source; dropping it would execute a partial recovery tree. No
recovery shape is admitted, and no second parser or recovery interpreter is
introduced. See [the boundary and repricing](sv-invalid-statements.md) and the
read-only instrument `extractors/sv/invalid_stmt_reprice.py`.

### Configurations — 2026-10-21

`ConfigBlockSymbol` is an elaboration-time design-selection boundary. In the
fresh 22,043-path census it occurs in 271 files: 148 configuration-only and
123 co-occurring. Those sole files contain 166 configuration blocks, 159
design clauses naming 168 top cells, 145 default-library rules, 23 cell rules,
58 instance rules and five configuration-localparam declarations. `use`
bindings, hierarchical instance matching, library precedence and
sub-configuration selection all change the elaborated design before the
existing single-top-module loader runs. No configuration shape is admitted by
dropping its declaration or selecting the first module; no second elaborator
or library resolver is introduced. See [the boundary and repricing](sv-configurations.md)
and the read-only instrument `extractors/sv/config_reprice.py`.

### Class declarations — 2026-10-21

`ClassType` remains the object-model boundary. In the fresh 22,043-path census
it occurs in 1,328 files: 109 class-only and 1,219 co-occurring. The sole
files contain 161 class spans: 95 ordinary classes, 29 classes with
`extends`, 32 interface classes and five virtual classes. Their spans include
100 method-bearing classes, 44 with random fields, 29 with constraints, four
with extern declarations and three with typedef members. Object identity,
allocation, inheritance, method frames, virtual dispatch and constrained
randomization are absent from the module store and executor. No class shape is
admitted by rewriting it as a module, and no random oracle or second scheduler
is introduced. See [the boundary and repricing](sv-classes.md) and the
read-only instrument `extractors/sv/class_reprice.py`.

### Nested class declarations — 2026-10-21

`ClassType:ClassType` is the separate module-member class boundary. In the
fresh 22,043-path census it occurs in 509 files: 49 are class-use-only and
460 co-occur with another wall. The sole files contain 65 nested class spans:
43 ordinary classes, 14 `extends` classes, six interface classes and two
virtual classes. Their spans include 25 method-bearing classes, 22 with
constraints, 18 with random fields, 16 with virtual/interface mentions, 17
with `extends` and five with covergroups. The module envelope has no object
identity, allocation, inheritance or class-member execution state, so no
nested class shape is admitted by flattening it into the containing module.
See [the boundary and repricing](sv-classes.md) and the read-only instrument
`extractors/sv/class_use_reprice.py`.

### Fork/join process control — 2026-10-21

The combined `fork ... join*` boundary covers the three frontend markers. In
the fresh 22,043-path census they occur in 571 files; 126 are fork/join-only
and 445 co-occur with another wall. The sole files contain 132 join blocks:
90 `join`/JoinAll, 10 `join_any` and 32 `join_none`. Child-process identity,
parent barriers, first-child release, detached-child lifetime and named-block
cancellation require scheduler state that the current surface envelope does
not carry. No join flavor is serialized or admitted, and no second scheduler
is introduced. See [the boundary and repricing](sv-fork-join.md) and the
read-only instrument `extractors/sv/fork_join_reprice.py`.

### Random sequence productions — 2026-10-21

`RandSequenceStatement` remains the constrained-random production boundary.
The fresh 22,043-path census records it in 72 files: 53 randsequence-only and
19 co-occurring. The sole files contain 54 production blocks, including 18
alternative, 15 conditional/case, 10 repeat, 10 weighted and 54 action-block
features (rows overlap). Production selection, random state, recursive
expansion and automatic action scopes have no representation in the current
envelope. No feature is admitted with a fixed branch or random guess, and no
second scheduler is introduced. See [the boundary and repricing](sv-randsequence.md)
and the read-only instrument `extractors/sv/randsequence_reprice.py`.


### Dynamic integral casts — 2026-10-20

IEEE §6.24.2/§20.5 dynamic integral casts now sample once, convert to the
destination width/state kind, and test an enum's exact bound member table.
Function failure returns zero without a destination write; success stores the
converted snapshot and returns one. Whole values, packed windows/members and
fixed cells use existing stores. The existing plusargs sequencer also sequences
casts, retaining logical short circuiting and refusing unordered dependencies.
Task success uses the same rule; invalid task diagnostics, unsupported types,
effects/contexts, invalid source and symbolic mode remain loud. No evaluator
or scheduler changes. See [the contract](sv-dynamic-cast.md).

The paired **22,035** paths gain **13 clean extractions**, no losses:
**4,296 → 4,309 clean**, **17,673 → 17,660 partial**, **66 include skips**,
zero errors. All 4,296 previously clean extracted designs remain identical.
Twelve gains match complete independent transcripts under both region oracles;
one retains the existing timed `$time` refusal. Six authored sources match
both orders, and four retain explicit boundaries. The invalid task reference
produces a runtime diagnostic and status one; it is not an agreement. Final
source/status/transcript/provenance authentication covers 22 successful
independent invocations plus that one diagnostic invocation. Six kernel
theorems bind the actual parsed source capture, membership guard and success
body. Extraction is distinct from whole-corpus runtime conformance.

See [the fixtures and receipts](../Examples/system-verilog/dynamic_cast/README.md).


### Fixed-array reduction methods — 2026-10-20

IEEE §7.12/§7.12.3 array `sum`, `product`, `and`, `or` and `xor` now use
intrinsic element/`with` widths and symbol-bound iterator substitution through
the existing fixed-cell storage and integral operations. Pure nested reductions,
packed fields, hierarchy, automatic lifetimes and timing compose. Dynamic
storage, unsupported types/effects/iterator queries, invalid source and symbolic
mode remain loud. No evaluator or scheduler changes. See [the contract](sv-array-reductions.md).

The paired **22,035** paths gain **11 clean extractions**, no losses:
**4,309 → 4,320 clean**, **17,660 → 17,649 partial**, **66 include skips**,
zero errors. All 4,309 previously clean extracted designs remain identical.
All eleven gains and six authored programs match complete independent
transcripts under both tested region oracles. Two authored programs retain
explicit refusals; they are not execution agreements. Nineteen final independent
invocations were authenticated. Four source-bound kernel theorems cover live
reads, modular arithmetic, copyback and source preservation. Extraction is
distinct from runtime conformance.

### Let expressions — 2026-10-20

IEEE §11.12 declarations at module, generate, package, compilation-unit,
hierarchy and procedural scopes now compile through the frontend's bound
expanded expressions. Declaration-scope binding, named/default actual structure,
context conversions, live values and NBA capture use the existing expression
and scheduler rules. The shared lexical-storage pass distinguishes same-spelled
locals; original syntax lookup rejects forward template uses, including macro
expansions. Invalid/redefined source and nonmodule scheduling stay loud.

Measured 33 clean-extraction gains and 12 withdrawn program admissions over
22,035 paths: 4,341 clean / 17,628 partial / 66 include skips / zero errors.
Twenty-nine gains, eleven existing binding regressions and seven authored
programs match full independent transcripts in both tested orders. Other runtime
refusals and unavailable typed/default-form oracle coverage remain explicit.
Four source-bound kernel theorems prove live reads, shadow independence,
modular addition and retained-work copyback. See [the contract](sv-let-expressions.md).

### Procedural variable lifetimes — 2026-10-20

IEEE §6.21/§9.3 static scalar, packed and fixed-array procedural declarations
now share pre-process storage initialization. Declaration re-entry is empty;
named-block hierarchy uses the original bound storage. Actual automatic scalar
entries retain `LocalDecl` and saved continuations through ordinary waits.
Nonclosed/effectful/order-dependent static initialization, invalid source and
implicit automatic-module default-lifetime disagreement remain loud.

Measured 20 clean-extraction gains and 35 withdrawn admissions over 22,035 paths:
4,326 clean / 17,643 partial / 66 include skips / zero errors. Nineteen gained
simulations and eight authored fixtures match full independent transcripts in
both tested orders. One compile-warning row remains horizon-limited; four
authored refusals are separate. The 1,141 changed prior clean designs show no
paired-model regression; that comparison is not independent conformance.
Four kernel theorems bind initialization and retained increments to actual source.
See [the contract](sv-procedural-lifetimes.md).

### Residual static initializers — 2026-10-22

`StaticLocal:initializer` remains the nonclosed static-initializer boundary.
The fresh 22,043-path census records it in 167 files: 40 are
initializer-only and 127 co-occur with another wall. The sole files contain
47 spans: nine random or constrained-random calls, 13 system-function calls,
three macro expansions, two package/qualified reads, seven type or size casts,
six real conversions, five shifts, three powers, five bitwise expressions, one
conditional, one aggregate assignment pattern and 39 runtime-dependent reads
(features overlap). Closed pure static values remain admitted; runtime,
effectful, package-dependent and otherwise nonclosed initializers need an
ordered evaluation contract absent from the envelope. No initializer is
folded, dropped or run as a module process, and no second scheduler is added.
See [the boundary and repricing](sv-static-initializers.md) and the read-only
instrument `extractors/sv/static_initializer_reprice.py`.

### Assignment-target boundary — 2026-10-21

The public target matrix remains limited to scalar identifiers, fixed packed
windows, direct untagged packed-struct/union fields, expanded fixed-array
cells, and the already-tested pure concatenation/streaming leaves. The fresh
22,043-path census records `AssignmentExpression:target` in 4,030 files; 43
are target-only and 3,987 have another refusal. Those 43 files contain 79
target instances, dominated by whole aggregate/array and dynamic element
destinations. The remaining rows mix procedural aggregate/slice/stream forms
with generated continuous drivers.

No additional legacy target subfamily is admitted in this rung. Aggregate
destinations need aggregate or net-driver state, and continuous targets need
the scheduler-owned driver path. Adding either as a surface shortcut would
fabricate storage or create a second scheduler. Existing packed/select/concat
fixtures remain the acceptance boundary; the full independent contract and
repricing table are in [assignment targets](sv-assignment-targets.md).

### Statement-call boundary — 2026-10-21

Statement-position calls remain limited to `$display`, `$write`, `$finish`,
and `$stop`, whose output and halt effects already have public state and
retained-continuation rules. The fresh 22,043-path census records
`ExpressionStatement:CallExpression` in 3,791 files: 261 call-only and 3,530
co-occurring. Their 498 call instances are dominated by `$fatal`, queue tasks,
dump tasks, `$strobe`/`$monitor`, and severity calls. Those require diagnostic,
Postponed, aggregate/device, external-I/O, or random-oracle representations;
none is an independent legacy admission. See [call statements](sv-call-statements.md).

### Call-expression boundary — 2026-10-21

Expression-position calls remain limited to fixed metadata queries, pure and
runtime `$clog2`, the time-zero `$time` literal, and dynamic integral `$cast`.
The 22,043-path census records `CallExpression` in 3,291 files: 212 call-only
and 3,079 co-occurring, with 315 call instances in the call-only set. Random
and distribution functions, sampled-value queries, time/real conversions,
external tasks, methods, and user calls require an oracle, scheduler history,
additional value/state representations, or callable frames. None is an
independent admission in this rung. See [call expressions](sv-call-expressions.md).

### Invalid elaboration diagnostics — 2026-10-22

`Elaboration:invalid-compilation` remains a design-level diagnostic boundary.
The fresh 22,043-path census records it in **33** files, all 33 as the sole
refusal. Those rows contain 17 generate-scope name conflicts (including
inactive and zero-entry blocks), four missing-generate-delimiter spans, three
nested-region spans, three generate-port declarations, two nonconstant
generate schemes, four illegal genvar uses, one generate end-label mismatch
and one macro conditional-expression error (features overlap).
The lowered generate representation has no partial-elaboration diagnostic
state, so no invalid prefix is salvaged and no recovery elaborator is added.
See [invalid elaboration diagnostics](sv-elaboration-invalid.md) and its
read-only repricer.

### `always_latch` inferred-sensitivity boundary — 2026-10-22

`ProceduralBlockSymbol:AlwaysLatch` remains a process-kind boundary. The fresh
22,043-path census records it in **53** files: 13 are latch-only and 40
co-occur. The 13 sole rows contain 12 inferred-sensitivity spans, six
nonblocking assignments, two mixed/timed companion-process rows, one explicit
timing-control diagnostic, one forbidden fork/join diagnostic, one
multiple-output latch, one nested-enable latch and one protected lexical
region (features overlap). The envelope has no inferred wait set, latch-hold
state or always-latch legality diagnostics, so the marker remains loud. See
[`always_latch`](sv-always-latch.md) and its read-only repricer.

### User-defined primitive boundary — 2026-10-22

`PrimitiveSymbol` remains the UDP declaration and truth-table boundary, separate
from built-in primitive instances. The fresh 22,043-path census records it in
**382** files: 13 are UDP-only and 369 co-occur. The 13 sole rows contain
three port-shape diagnostics, one combinational current-state field, two all-X
input rows with non-X output/next-state, one duplicate-input row, three rows
with multiple transitions, one missing input field, one `z` table symbol and
one invalid initial output value. UDP state tables need a declaration and
transition matcher absent from the envelope; no table evaluator or driver is
introduced. See [the UDP boundary](sv-udp.md).

### Concurrent sequence declaration boundary — 2026-10-22

`SequenceSymbol:Sequence` remains a sampled-concurrent sequence boundary. The
fresh 22,043-path census records it in **284** files: 12 are sequence-only and
272 co-occur. The independent repricer finds **15** sequence spans in the sole
files. Overlapping features include five local-variable spans, four formal
arguments, seven multiclock rows, one `intersect`, nine temporal
concatenations, two matched endpoints, one end label, one event/local
diagnostic, two sequence-typed formals and two sampled-value functions. The
envelope has no sequence-attempt, sampled-history or local/formal frame, so no
sequence is lowered to a Boolean or immediate assertion. See [the sequence
boundary](sv-sequences.md).

### Residual module typedef boundary — 2026-10-22

`TypeAliasType:TypeAlias` remains the residual module-scope typedef boundary
beside the already-admitted integral alias slice. The fresh 22,043-path census
records it in **299** files: 12 are alias-only and 287 co-occur. The sole rows
contain eight `$bits` queries, nine aggregate typedefs, three enum typedefs,
two enum-member redefinitions, one nonpositive enum range and one
nonconstant struct-member initializer (features overlap). The envelope has no
general aggregate type descriptor or rejected-alias diagnostic state, so these
aliases remain loud. See [residual module typedefs](sv-type-alias-boundary.md).

### Compilation-unit aggregate typedef boundary — 2026-10-22

The fresh 22,043-path census records `TypeAliasType` in **116** files: **12**
are unit-alias-only and 104 co-occur. Repricing those sole files finds **13**
overlapping aggregate and union spans: seven nonintegral packed members, one
packed-union width mismatch, two packed-dimension qualifiers, one unpacked
struct-signing diagnostic, two union-member defaults, one void member in an
untagged union, two packed tagged-union shapes, two tagged-union dynamic
members and one untagged-union dynamic member. The legacy envelope has no
aggregate layout, tagged-union state or dynamic-member representation, so
these compilation-unit aliases remain loud. See [compilation-unit aggregate
typedefs](sv-unit-type-aliases.md).

### Element-select source-type boundary — 2026-10-22

The fresh 22,043-path census records `ElementSelectExpression:source-type` in
**662** files: **11** are sole refusals and 651 co-occur. Repricing those sole
files finds **23** selection spans: one scalar bit-select diagnostic, 17 nested
packed-union member selections, two two-state unpacked-array out-of-bounds
reads, two four-state out-of-bounds reads and one enum-array base-type result.
The selected-read envelope has no general aggregate layout or
state-kind-specific out-of-bounds rule, so it does not flatten a union, invent
a scalar index or choose an unknown/zero result. See [element-select
source types](sv-element-select-source.md).

### Package subroutine boundary — 2026-10-22

The fresh 22,043-path census records `Package:Subroutine` in **194** files:
**10** are sole refusals and 184 co-occur. Repricing those sole files finds
**12** spans: ten package function declarations, nine constant-function uses,
one nonconstant package function and two DPI imports. The declaration and
constant-use labels overlap. Package callable tables, constant-function
frames and DPI linkage are absent from the legacy envelope, so no package
subroutine is erased or inlined. See [package subroutines](sv-package-subroutines.md).

### Inout port boundary — 2026-10-22

The fresh 22,043-path census records `PortSymbol:InOut` in **10** files: **9**
are sole refusals and one co-occurs. Repricing the sole files finds **14**
spans: five generic-interface non-ANSI diagnostics, two unpacked-dimension
inheritance cases, two integer-to-signed resets, two packed-dimension-to-wire
resets, one inout initializer, one interconnect initializer and one signed
interconnect port. Bidirectional aliasing, resolution and port declaration
state are absent from the envelope, so no inout is rewritten. See [inout
ports](sv-inout-ports.md).

### Variable type boundary — 2026-10-22

The fresh 22,043-path census records `VariableSymbol:type` in **150** files:
**10** are sole refusals and 140 co-occur. Repricing the sole files finds
**10** variable spans: nine fixed unpacked-array storage declarations (seven
multidimensional), nine packed-element-plus-unpacked declarations and one
invalid packed dimension on an aggregate. The labels overlap. The legacy
envelope has no aggregate runtime store or invalid-type recovery state, so no
variable is flattened or fabricated. See [variable types](sv-variable-types.md).

### Compilation-unit variable boundary — 2026-10-22

The fresh 22,043-path census records `VariableSymbol` in **76** files: **10**
are sole refusals and 66 co-occur. Repricing the sole files finds **10** spans:
nine compilation-unit variable declarations, two multiple-top-level-module
rows, one enum-range declaration and one invalid packed dimension on `int`.
The compilation-unit and multiple-top-level labels overlap, as does the
invalid declaration's unit-scope label. The envelope has no `$unit` store or
multiple-top-level hierarchy contract, so these variables remain loud. See
[compilation-unit variables](sv-compilation-unit-variables.md).

### Case-subject boundary — 2026-10-22

The fresh 22,043-path census records `CaseStatement:subject` in **30** files:
**8** are sole refusals and 22 co-occur. Repricing the sole files finds **8**
spans: five `$time` subjects, one constant-expression subject, one packed-union
member subject and one packed-struct part-select subject. The ordinary case
chain has no general time, elaboration-constant or aggregate subject plan, so
no subject is replaced or flattened. See [case subjects](sv-case-subjects.md).

### Net type boundary — 2026-10-22

The fresh 22,043-path census records `NetSymbol:type` in **24** files: **7**
are sole refusals and 17 co-occur. Repricing the sole files finds **7** net
spans: four multidimensional net arrays, one generated net-array case, two
packed-struct nets and one typedef-struct net. The array labels overlap. Net
driver storage and aggregate field identity are absent from the envelope, so
no net is flattened or given a variable store. See [net types](sv-net-types.md).

### `supply1` net boundary — 2026-10-22

The fresh 22,043-path census records `NetSymbol:Supply1` in **56** files: **5**
are sole refusals and 51 co-occur. Repricing the sole files finds **5** supply
spans: all five carry a supply-strength logic-one driver, and one also tests a
continuous-assignment strength context. The envelope has no strength lattice
or supply driver set, so `supply1` is not replaced by a constant. See
[the `supply1` boundary](sv-supply1.md).

### Variable packed-range boundary — 2026-10-22

The fresh 22,043-path census records `VariableSymbol:range` in **62** files:
**7** are sole refusals and 55 co-occur. Repricing the sole files finds **7**
unsupported range spans: four multidimensional packed ranges and three packed-
struct array ranges. The legacy variable representation has no complete
multidimensional range descriptor, so these dimensions remain loud. See
[variable packed ranges](sv-variable-ranges.md).

### Explicit conversion boundary — 2026-10-22

The fresh 22,043-path census records `ConversionExpression:Explicit` in **37**
files: **7** are sole refusals and 30 co-occur. Repricing the sole files finds
21 real-to-integral rounding casts and one typed assignment-pattern cast. The
legacy expression value has no real representation, general cast operator or
aggregate pattern layout, so explicit casts remain loud. See
[explicit conversions](sv-explicit-casts.md).

### Invalid hierarchy boundary — 2026-10-22

The fresh 22,043-path census records `Hierarchy:invalid-compilation` in **329**
files: **7** are sole refusals and 322 co-occur. Repricing the sole files
finds seven rejected hierarchy spans covering localparam overrides, parameter
assignment order/duplication, zero-port instance syntax and a hierarchical
`type()` reference. The envelope has no partial-hierarchy diagnostic state,
so rejected designs remain loud. See [invalid hierarchies](sv-invalid-hierarchies.md).

### Conditional event (`iff`) boundary — 2026-10-22

The fresh 22,043-path census records `SignalEventControl:iff` in **7** files;
all **7** are sole refusals. Repricing finds four procedural event guards,
two `always_ff` guards and one procedural `always` guard, with three edge and
four level-qualified forms. The wait representation has no occurrence-time
guard or inferred-clock state, so `iff` controls remain loud. See
[conditional events](sv-event-iff.md).

### Invalid static-local boundary — 2026-10-22

The fresh 22,043-path census records `StaticLocal:invalid-compilation` in
**241** files: **7** are sole refusals and 234 co-occur. Repricing the sole
files finds seven rejected static-local spans covering lexical errors,
declaration ordering and block-label syntax. The envelope has no recovery frame
or diagnostic stream, so malformed blocks remain loud. See [invalid static locals](sv-invalid-static-locals.md).

### Invalid continuous-assignment boundary — 2026-10-22

The fresh 22,043-path census records `ContinuousAssignSymbol:InvalidExpression`
in **14** files: **6** are sole refusals and 8 co-occur. Repricing the sole
files finds seven rejected assignment spans involving `default_nettype none`,
invalid `supply0`/`supply1` directives and `undefineall` state. The envelope has
no implicit-net diagnostic state, so these assignments remain loud. See
[invalid continuous assignments](sv-invalid-continuous-assignments.md).

### Empty-member boundary — 2026-10-22

The fresh 22,043-path census records `EmptyMemberSymbol:EmptyMember` in **57**
files: **6** are sole refusals and 51 co-occur. Repricing the sole files finds
six empty-member spans covering soft-keyword mode, unnamed primitive arrays,
nested attributes and dollar-leading identifiers. The envelope has no recovery
node or diagnostic stream, so these members remain loud. See
[empty members](sv-empty-members.md).

### Assignment-pattern boundary — 2026-10-22

The fresh 22,043-path census records `AssignmentPattern:integral-shape` in
**5** files, all sole refusals. Repricing finds **10** typed packed pattern
spans, each using a casted nested pattern in a concatenation. The envelope has
no self-determined aggregate layout, so these patterns remain loud. See
[assignment patterns](sv-assignment-pattern-boundary.md).

### Bitwise XNOR boundary — 2026-10-22

The fresh 22,043-path census records `BinaryExpression:BinaryXnor` in **7**
files: **5** are sole refusals and 2 co-occur. Repricing the sole files finds
**10** spans across the `~^` and `^~` spellings, with variable and literal
operands. The binary evaluator has no four-state XNOR rule, so these operators
remain loud. See [bitwise XNOR](sv-xnor.md).

### Pattern-condition boundary — 2026-10-22

The fresh 22,043-path census records `ConditionalStatement:pattern` in **12**
files: **5** are sole refusals and 7 co-occur. Repricing the sole files finds
**9** spans covering constant integral, identifier-binding and structure member
or wildcard patterns. The conditional evaluator has no pattern binding or
aggregate-member state, so these conditions remain loud. See
[pattern conditions](sv-pattern-conditions.md).

### Elaboration system-task boundary — 2026-10-22

The fresh 22,043-path census records `ElabSystemTaskSymbol:ElabSystemTask` in
**12** files: **5** are sole refusals and 7 co-occur. Repricing finds six
elaboration-task spans containing `$info` and `$warning`. The envelope has no
pre-simulation diagnostic phase, so these tasks remain loud. See
[elaboration system tasks](sv-elaboration-system-tasks.md).

### Hierarchy timescale boundary — 2026-10-22

The fresh 22,043-path census records `Hierarchy:timescale` in **27** files:
**5** are sole refusals and 22 co-occur. Repricing finds five hierarchy spans
with per-module directives and time observations or delays. The hierarchy has
no scoped time-unit environment, so these designs remain loud. See
[hierarchy timescales](sv-timescale.md).

### `supply0` net boundary — 2026-10-22

The fresh 22,043-path census records `NetSymbol:Supply0` in **48** files:
**5** are sole refusals and 43 co-occur. Repricing finds five supply-strength
net spans, including one continuous-strength context. The envelope has no
strength lattice or supply driver set, so `supply0` remains loud. See
[`supply0`](sv-supply0.md).

### System-call format boundary — 2026-10-22

The fresh 22,043-path census records `SysCall:format` in **6** files: **5**
are sole refusals and one co-occurs. Repricing finds five format spans, four
macro default/empty-argument cases and one runtime display format. The envelope
has no macro-expansion trace or format-argument model, so these calls remain
loud. See [system-call formatting](sv-syscall-format.md).

### Compilation-unit parameter boundary — 2026-10-22

The fresh 22,043-path census records `ParameterSymbol` in **25** files: **5**
are sole refusals and 20 co-occur. Repricing finds five compilation-unit
parameter spans, with `$unit::` references, module-parameter context and
shadowing among the source shapes. The envelope has no unit parameter store or
scope resolver, so these parameters remain loud. See [parameter scope](sv-parameter-scope.md).

### Residual two-state named-value boundary — 2026-10-22

The fresh 22,043-path census records `NamedValueExpression:2state` in **1,482**
files: **5** are sole refusals and 1,477 co-occur. Repricing finds five fixed-
array named-value spans covering unpacked concatenation, indexed patterns,
array literals and descending `foreach`. The aggregate store and range resolver
are absent, so these names remain loud. See [residual two-state named values](sv-namedvalue-2state.md).

### Invalid enumeration boundary — 2026-10-22

The fresh 22,043-path census records `Enum:invalid-compilation` in **36**
files: **4** are sole refusals and 32 co-occur. Repricing finds four rejected
enum spans: three X/Z values on two-state bases and one duplicate value. The
enum representation has no invalid-declaration state, so these remain loud. See
[invalid enums](sv-invalid-enums.md).

### Large fixed-array sparse cells — 2026-10-23

The self-check tier now admits one-dimensional fixed unpacked integral arrays
whose extent is larger than the flat-state expansion limit when every use is a
constant element selection. Ingestion materializes only the observed cells,
retaining two-state zero startup and ordinary assignment semantics. Dynamic,
whole-array, aggregate, and nonintegral uses remain loud. The
`large_fixed_array` fixture covers the IEEE minimum 2^24-element declaration.

### Unused string literal initializers — 2026-10-23

Declaration-only module and local `string` variables may now carry a pure
string-literal initializer when the value is never read. The declaration is
omitted from the flat vector state, while nonliteral initializers and every
string operation remain loud. The `string_literal_decl` fixture covers both
module and local declarations.

### Pure string literal writes — 2026-10-23

Procedural assignments of a pure string literal to an opaque string are erased
as no-op state updates. Nonliteral writes and every string read or operation
remain loud. The `do_while_string_literal` fixture supplies differential
coverage for this assignment slice.

### Runtime severity diagnostics — 2026-10-23

Statement-position `$info` and `$warning` calls with only string-literal
arguments now lower to inert `Empty` statements. IEEE 1800-2023 §20.10 says
these tasks report diagnostics without terminating simulation; the public
self-check state has no diagnostic stream, so erasing a pure call preserves
the modeled control flow. Dynamic arguments, `$fatal`, and all other
unmodeled system calls remain loud. The `severity_tasks` fixture and
differential row cover the admitted form. The 22,035-file census moves from
**4,442 → 4,462 clean** and **17,527 → 17,507 partial**; the
`ExpressionStatement:CallExpression` blocker falls **3,784 → 3,764**.

### Declaration-only 2-state queues — 2026-10-23

An uninitialized 2-state queue declaration now lowers to inert metadata, so a
queue that has no admitted operation does not create a false `Variable` state
slot. Queue initializers, reads, writes, methods, and all 4-state queues remain
loud because their value and mutation semantics are not represented in the
self-check state. The `queue_decl` fixture and differential row cover the
declaration-only form. The census keeps **4,462 clean / 17,507 partial** and
reduces `VariableSymbol:2state` **3,989 → 3,839**; differential coverage is
**32 rows, 28 matches, 0 disagreements, and 4 recorded refusals**, with
**200 grammar witnesses, 68 MATCH, and 132 REFUSE**.

### Literal severity-task arguments — 2026-10-23

Runtime `$info` and `$warning` calls with a literal format and literal
arguments now lower to inert statements. Identifier, query, and call
arguments remain loud because evaluating them may have effects; `$fatal` remains
outside the slice. The `severity_task_literals` fixture and
differential row cover the extension. The census moves **4,462 → 4,467 clean**
and **17,507 → 17,502 partial**; `ExpressionStatement:CallExpression` falls
**3,764 → 3,759**. Differential coverage is **34 rows, 30 matches, 0
disagreements, and 4 recorded refusals**.

### Literal `$error` diagnostics — 2026-10-23

Statement-position `$error` with a literal format and literal arguments now
lowers to an inert statement. IEEE 1800-2023 §20.10 specifies that `$error`
reports a runtime diagnostic and does not terminate simulation, so removing
the unmodeled diagnostic stream preserves the self-check control flow.
Nonliteral arguments and `$fatal` remain loud. The `error_task` fixture and
differential row cover the admitted form. The census moves **4,467 → 4,476
clean** and **17,502 → 17,493 partial**; `ExpressionStatement:CallExpression`
falls **3,759 → 3,749**. Differential coverage is **35 rows, 31 matches, 0
disagreements, and 4 recorded refusals**.

### Literal `$fatal` termination — 2026-10-23

Statement-position `$fatal` with only literal arguments now lowers to the
existing whole-run halt. This preserves its terminating control-flow effect
while omitting the diagnostic stream absent from the self-check state. Dynamic
finish numbers and message arguments remain loud. The `fatal_task` fixture and
differential row cover the admitted form. The census moves **4,476 → 4,505
clean** and **17,493 → 17,464 partial**; `ExpressionStatement:CallExpression`
falls **3,749 → 3,602**. Differential coverage is **36 rows, 32 matches, 0
disagreements, and 4 recorded refusals**.

### Declaration-only 2-state dynamic arrays — 2026-10-23

An uninitialized 2-state dynamic-array declaration now lowers to inert
metadata. Allocation, initializers, reads, writes, and all other dynamic-array
operations remain loud because the self-check state has no dynamic storage
model. The `dynamic_array_decl` fixture and differential row cover this
declaration-only form. Clean and partial totals remain **4,462 / 17,507**;
`VariableSymbol:2state` falls **3,839 → 3,691**. Differential coverage is
**33 rows, 29 matches, 0 disagreements, and 4 recorded refusals**, with **200
grammar witnesses, 68 MATCH, and 132 REFUSE**.

### Declaration-only 2-state associative arrays — 2026-10-23

An uninitialized 2-state associative-array declaration now lowers to inert
metadata. Initializers, reads, writes, and all 4-state associative arrays
remain loud because the self-check state has no associative storage model.
The `associative_array_decl` fixture and differential row cover this
declaration-only form. The census moves **4,505 → 4,506 clean** and
**17,464 → 17,463 partial**; `VariableSymbol:2state` falls **3,691 → 3,501**.
Differential coverage is **37 rows, 33 matches, 0 disagreements, and 4
recorded refusals**, with **200 grammar witnesses, 68 MATCH, and 132 REFUSE**.

### Inert no-argument `$printtimescale` — 2026-10-23

The no-argument `$printtimescale` task now lowers to an inert diagnostic
statement. Explicit scope arguments and other time-format tasks remain loud
because hierarchy and time-scale state are outside the self-check model. The
`printtimescale_decl` fixture and differential row cover the admitted form.
The census moves **4,506 → 4,507 clean** and **17,463 → 17,462 partial**;
`ExpressionStatement:CallExpression` falls **3,602 → 3,599**. Differential
coverage is **38 rows, 34 matches, 0 disagreements, and 4 recorded refusals**;
grammar coverage is **200 witnesses, 69 MATCH, and 131 REFUSE**.

### Inert module-originating `$exit` — 2026-10-23

The module-originating `$exit` task now lowers to an inert statement, matching
IEEE 1800-2023 §24.7's rule that `$exit` is ignored outside a
program-originating process. Program process control and other contexts remain
loud. The `exit_decl` fixture and differential row cover the admitted form.
The census moves **4,507 → 4,511 clean** and **17,462 → 17,458 partial**;
`ExpressionStatement:CallExpression` falls **3,599 → 3,595**. Differential
coverage is **39 rows, 35 matches, 0 disagreements, and 4 recorded refusals**;
grammar coverage remains **200 witnesses, 69 MATCH, and 131 REFUSE**.

### Inert VCD setup tasks — 2026-10-23

`$dumpfile` and `$dumpvars` now lower to inert statements because their only
effect is external waveform output outside the self-check observable state.
Literal or omitted `$dumpfile` names are admitted; dynamic names remain loud.
The `vcd_setup` fixture and differential row cover the admitted form. The
census moves **4,511 → 4,525 clean** and **17,458 → 17,444 partial**;
`ExpressionStatement:CallExpression` falls **3,595 → 3,580**. Differential
coverage is **40 rows, 36 matches, 0 disagreements, and 4 recorded refusals**;
grammar coverage remains **200 witnesses, 69 MATCH, and 131 REFUSE**.

### Inert VCD control tasks — 2026-10-23

`$dumpon`, `$dumpoff`, `$dumpall`, `$dumpflush`, and literal `$dumplimit` now
lower to inert statements because they affect only external waveform recording.
Dynamic size limits remain loud. The `vcd_control` fixture and differential row
cover the admitted form. The census moves **4,525 → 4,540 clean** and
**17,444 → 17,429 partial**; `ExpressionStatement:CallExpression` falls
**3,580 → 3,565**. Differential coverage is **41 rows, 37 matches, 0
disagreements, and 4 recorded refusals**; grammar coverage remains **200
witnesses, 69 MATCH, and 131 REFUSE**.

### Unpacked integral struct copies — 2026-10-23

Whole copies of flattened integral unpacked structs now lower field by field,
sampling the source before destination writes. Aggregate fields and self-copies
remain loud. The `unpacked_struct_copy` fixture and differential row cover the
admitted form. The census moves **4,540 → 4,552 clean** and **17,429 → 17,417
partial**; `AssignmentExpression:target` falls **3,592 → 3,580**. Differential
coverage is **42 rows, 38 matches, 0 disagreements, and 4 recorded refusals**;
grammar coverage remains **200 witnesses, 69 MATCH, and 131 REFUSE**.

### Unpacked integral struct positional patterns — 2026-10-23

Complete positional assignment patterns for flattened integral unpacked structs
now lower field by field in elaborated declaration order. Each destination cell
keeps its declared width and two-state `Squash2` conversion, while incomplete,
nested, aggregate, effectful, and nonintegral patterns remain loud. The
`unpacked_struct_pattern` fixture and differential row cover the admitted form;
the focused extractor regression checks field order and two-state preservation.
The census moves **4,552 → 4,558 clean** and **17,417 → 17,411 partial**;
`AssignmentExpression:target` falls **3,580 → 3,568**. Differential coverage
is **43 rows, 39 matches, 0 disagreements, and 4 recorded refusals**; grammar
coverage remains **200 witnesses, 69 MATCH, and 131 REFUSE**.

### Unpacked integral struct keyed patterns — 2026-10-23

Complete keyed assignment patterns for flattened integral unpacked structs now
reuse the fieldwise lowering, with pyslang's elaborated elements preserving
declaration order regardless of source key order. Each field keeps its width and
two-state conversion; incomplete, nested, aggregate, effectful, and
nonintegral patterns remain loud. The `unpacked_struct_keyed_pattern` fixture
and differential row cover this form, alongside the focused field-order
regression. The census moves **4,558 → 4,577 clean** and **17,411 → 17,392
partial**; `AssignmentExpression:target` falls **3,568 → 3,542**. Differential
coverage is **44 rows, 40 matches, 0 disagreements, and 4 recorded refusals**;
grammar coverage remains **200 witnesses, 69 MATCH, and 131 REFUSE**.

### Validated-scope `$printtimescale` — 2026-10-23

`$printtimescale` with `$unit`, `$root`, or a validated instance scope now
lowers to the same inert diagnostic node as the no-argument form. Invalid,
dynamic, and malformed scope expressions remain loud because hierarchy and
time-scale state are outside the self-check observable model. The
`printtimescale_scope` fixture and differential row cover the three admitted
scope categories. The census moves **4,577 → 4,582 clean** and **17,392 →
17,387 partial**; `ExpressionStatement:CallExpression` falls **3,565 →
3,558**. Differential coverage is **45 rows, 41 matches, 0 disagreements, and
4 recorded refusals**; grammar coverage is **202 witnesses, 69 MATCH, and 133
REFUSE**.

### Literal `$strobe` output — 2026-10-23

Literal-format `$strobe` calls now queue a self-check output event and flush it
after all active time-zero statements, preserving the IEEE Postponed ordering
relative to `$display`. Dynamic or effectful arguments, file variants, and
other timing-dependent forms remain loud. The `strobe_literal` fixture and
differential row cover the deferred ordering; the self-check runner carries a
pending strobe queue without adding a second scheduler. The census moves
**4,582 → 4,585 clean** and **17,387 → 17,384 partial**;
`ExpressionStatement:CallExpression` falls **3,558 → 3,555**. Differential
coverage is **46 rows, 42 matches, 0 disagreements, and 4 recorded refusals**;
grammar coverage remains **202 witnesses, 69 MATCH, and 133 REFUSE**.

### Conditional integral unpacked-struct assignments — 2026-10-23

Assignments of a pure conditional expression between flattened integral
unpacked structs now lower one ternary per field, sampling the condition once
and retaining four-state conditional merging. Aggregate fields, effectful
conditions, and destination/source aliasing remain loud. The
`unpacked_struct_conditional` fixture and differential row cover both branches.
On the 22,045-file corpus snapshot, clean files move **4,593 → 4,594** and
partial files **17,386 → 17,385**; `AssignmentExpression:target` falls
**3,546 → 3,545**. Differential coverage is **50 rows, 46 matches, 0
disagreements, and 4 recorded refusals**; grammar coverage remains **202
witnesses, 71 MATCH, and 131 REFUSE**.

### Nested fixed-array assignment patterns — 2026-10-23

Complete assignment patterns over finite multidimensional unpacked arrays now
flatten through every dimension into ordinary vector-cell writes. Replication
is expanded at each dimension, source cells are sampled before writes, and
dynamic, partial, aliased, or aggregate-element patterns remain loud. The
`unpacked_array_nested_pattern` fixture and differential row cover nested
replication. On the 22,045-file corpus snapshot, clean files move **4,604 →
4,612** and partial files **17,375 → 17,367**; `AssignmentExpression:target`
falls **3,535 → 3,524**. Differential coverage is **52 rows, 48 matches, 0
disagreements, and 4 recorded refusals**; grammar coverage remains **202
witnesses, 71 MATCH, and 131 REFUSE**.

### Nested integral unpacked-struct patterns — 2026-10-23

Complete nested assignment patterns for flattened integral unpacked structs now
reuse the recursive declaration flattener, preserving declaration order,
recursive `default` values, leaf widths, and two-state conversion. Unsupported
aggregate leaves and incomplete patterns remain loud. The
`unpacked_struct_nested_pattern` fixture and differential row cover explicit
and default nested patterns. On the 22,045-file corpus snapshot, clean files
move **4,594 → 4,604** and partial files **17,385 → 17,375**;
`AssignmentExpression:target` falls **3,545 → 3,535**. Differential coverage is
**51 rows, 47 matches, 0 disagreements, and 4 recorded refusals**; grammar
coverage remains **202 witnesses, 71 MATCH, and 131 REFUSE**.

### Fixed-array patterns with integral struct elements — 2026-10-23

Complete positional patterns whose elements are finite integral unpacked structs
now flatten each array row and struct field into ordinary scalar writes. The
existing recursive struct flattener preserves field order and two-state
conversion, while incomplete, dynamic, aggregate, and aliased patterns remain
loud. The `fixed_array_struct_pattern` fixture and differential row cover
complete row patterns. The 22,046-file census moves **4,622 → 4,624 clean**
and **17,358 → 17,356 partial**; `AssignmentExpression:target` falls
**3,512 → 3,510**. Differential coverage is **60 rows, 56 matches, 0
disagreements, and 4 recorded refusals**; grammar coverage is now **203
witnesses, 72 MATCH, and 131 REFUSE**.

### Dynamic `$fatal` arguments — 2026-10-23

`$fatal` now evaluates pure dynamic severity, format, and value arguments in
source order before halting the self-check run. The diagnostic stream remains
outside the observable state, while effectful calls and unsupported argument
expressions remain loud. The `fatal_dynamic` fixture and differential row cover
the dynamic path; the focused extractor regression keeps effectful arguments
refused. On the current 22,045-file corpus snapshot, the census moves **4,589
→ 4,593 clean** and **17,390 → 17,386 partial**; the
`ExpressionStatement:CallExpression` blocker falls **3,559 → 3,475**.
Differential coverage is **49 rows, 45 matches, 0 disagreements, and 4 recorded
refusals**; grammar coverage remains **202 witnesses, 71 MATCH, and 131 REFUSE**.

### Standard-output `$fdisplay` — 2026-10-23

`$fdisplay` with the predefined standard-output descriptor (`1` or
`32'h8000_0001`) now reuses the existing `$display` renderer and observable
output stream. Other file descriptors, dynamic handles, and file-output task
variants remain loud because the self-check state has no file system model. The
`fdisplay_stdout` fixture and differential row cover the admitted descriptor
slice. The census moves **4,585 → 4,586 clean** and **17,384 → 17,383 partial**;
`ExpressionStatement:CallExpression` falls **3,555 → 3,554**. Differential
coverage is **47 rows, 43 matches, 0 disagreements, and 4 recorded refusals**;
grammar coverage remains **202 witnesses, 69 MATCH, and 133 REFUSE**.

### Dynamic severity-task arguments — 2026-10-23

`$info`, `$warning`, and `$error` with a literal format and ordinary pure
expression arguments now evaluate those arguments in order and discard only
the diagnostic stream, which is outside the self-check observable output.
Effectful calls, nonliteral formats, and unsupported expression forms remain
loud. The `severity_dynamic` fixture and differential row cover reads,
literal strings, and all three severity tasks. The census moves **4,586 →
4,589 clean** and **17,383 → 17,380 partial**;
`ExpressionStatement:CallExpression` falls **3,554 → 3,551**. Differential
coverage is **48 rows, 44 matches, 0 disagreements, and 4 recorded refusals**;
grammar coverage remains **202 witnesses, 69 MATCH, and 133 REFUSE**.

### Recursive nested-array streaming unpack — 2026-10-23

Unsized right-streaming assignment now admits a complete finite multidimensional
fixed unpacked array of integral leaves. The extractor flattens the array in
declared dimension order into the existing scalar-cell `ConcatTarget`, so the
MSB-first sampled source window and per-cell two-state conversion remain the
same as explicit scalar targets. Partial subarrays, dynamic selections, sized
or left streams, aggregate leaves, and streaming `with` clauses remain loud.
The `streaming_nested_fixed_array` fixture and differential row cover the
recursive target shape. The 22,046-file census moves **4,615 → 4,616 clean**
and **17,365 → 17,364 partial**; `AssignmentExpression:target` falls **3,520
→ 3,519**. Differential coverage is **56 rows, 52 matches, 0 disagreements,
and 4 recorded refusals**; grammar coverage remains **202 witnesses, 71 MATCH,
and 131 REFUSE**.

### Fixed-slice left-streaming targets — 2026-10-23

Explicit positive-slice left streaming now admits direct integral target leaves
whose widths equal the slice size. The first target receives the source's
least-significant chunk, followed by the remaining chunks in source order,
preserving the sampled vector and existing two-state behavior. Unsized or
dynamic targets, streaming `with` clauses, partial arrays, nested aggregates,
and mixed-state windows remain loud. The `streaming_left_target` fixture and
differential row cover the byte-reversal form, with symbolic and legacy
extractor regressions for chunk geometry. The census moves **4,616 → 4,617
clean** and **17,364 → 17,363 partial**; `AssignmentExpression:target` falls
**3,519 → 3,518**. Differential coverage is **57 rows, 53 matches, 0
disagreements, and 4 recorded refusals**; grammar coverage remains **202
witnesses, 71 MATCH, and 131 REFUSE**.

### Runtime indexed slices of fixed unpacked arrays — 2026-10-23

Constant-width indexed part-select assignment over distinct bounded
one-dimensional integral unpacked arrays now lowers to guarded per-cell writes.
`IndexedUp` and `IndexedDown` preserve their source and destination directions;
runtime starts are evaluated once and source cells are read through a complete
conditional snapshot before the destination block executes. Invalid windows,
dynamic or nonpositive widths, nested or aggregate arrays, and alias-sensitive
self-copies remain loud. The `fixed_array_indexed_slice` fixture and
differential row cover the `A[i+:c] = B[j+:c]` form. The 22,046-file census
moves **4,617 → 4,618 clean** and **17,363 → 17,362 partial**;
`AssignmentExpression:target` falls **3,518 → 3,517**. Differential coverage is
**58 rows, 54 matches, 0 disagreements, and 4 recorded refusals**; grammar
coverage remains **202 witnesses, 71 MATCH, and 131 REFUSE**.

### Integral bit-stream casts into fixed unpacked arrays — 2026-10-23

Bit-stream casts from an integral source into a complete finite fixed unpacked
array now lower to scalar leaf writes in declaration order, with element zero
receiving the source's most-significant bits. Equal total widths, integral
leaves, and two-state conversion are checked before admission; dynamic arrays,
queues, aggregate leaves, and mismatched widths remain loud. The
`fixed_array_bitstream_cast` fixture and differential row cover the
`bytes = bytes_t'(bits)` form. The 22,046-file census moves **4,618 → 4,622
clean** and **17,362 → 17,358 partial**; `AssignmentExpression:target` falls
**3,517 → 3,512**. Differential coverage is **59 rows, 55 matches, 0
disagreements, and 4 recorded refusals**; grammar coverage remains **202
witnesses, 71 MATCH, and 131 REFUSE**.

### Generated constant packed targets — 2026-10-23

Elaboration-constant packed element targets in generated assignments now
normalize their bound genvar arithmetic to fixed bit windows. This admits the
ordinary generated-chain and stepped-genvar assignments while retaining the
existing dynamic-index boundary. The `generate_constant_targets` fixture and
differential row cover the chained generated writes. The 22,046-file census
moves **4,639 → 4,645 clean** and **17,341 → 17,335 partial**;
`AssignmentExpression:target` falls **3,507 → 3,500**. Differential coverage
is **61 rows, 57 matches, 0 disagreements, and 4 recorded refusals**; grammar
coverage remains **203 witnesses, 72 MATCH, and 131 REFUSE**.

### Uninitialized procedural floating declarations — 2026-10-23

An uninitialized `real` or `shortreal` declaration inside a procedural
context now lowers to an empty declaration because floating storage is outside
the self-check state and the declaration has no initializer effect. Reads and
initialized declarations remain loud at their existing expression or
declaration boundaries. The `floating_local_decl` fixture and differential row
cover the admitted declaration shape. The 22,046-file census moves **4,645 →
4,645 clean** and **17,335 → 17,335 partial**; `VariableSymbol:2state` falls
**3,504 → 3,369** after the fresh census. Differential coverage is **62 rows,
58 matches, 0 disagreements, and 4 recorded refusals**; grammar coverage is
**203 witnesses, 72 MATCH, and 131 REFUSE**.

### Right-streaming packed-struct sources into array cells — 2026-10-23

Unsized right-streaming assignment now accepts a packed struct source streamed
into direct integral unpacked-array cells. The source stream is lowered to its
single sampled packed vector, then split across the target cells in declaration
order; nested streams, partial arrays, and `with` clauses remain loud. The
`streaming_struct_source` fixture and differential row cover the
§11.4.14.1 declaration-order case. The 22,046-file census moves **4,652 →
4,653 clean** and **17,328 → 17,327 partial**; `AssignmentExpression:target`
falls **3,493 → 3,492**. Differential coverage is **65 rows, 61 matches, 0
disagreements, and 4 recorded refusals**; grammar coverage remains **203
witnesses, 72 MATCH, and 131 REFUSE**.

### Out-of-bounds fixed-array unpacked-struct reads — 2026-10-23

Assignments from a fully constant out-of-bounds fixed unpacked-array element
now admit unpacked struct leaves. The extractor expands the destination fields
and supplies each field's IEEE §7.4.5 default, including a declared member
initializer; aggregate leaves, dynamic indices, and non-struct out-of-bounds
forms remain loud. The `oob_struct_read` fixture and differential row cover
the initialized and type-default fields. The 22,046-file census moves
**4,649 → 4,652 clean** and **17,331 → 17,328 partial**;
`AssignmentExpression:target` falls **3,496 → 3,493**. Differential coverage
is **64 rows, 60 matches, 0 disagreements, and 4 recorded refusals**; grammar
coverage remains **203 witnesses, 72 MATCH, and 131 REFUSE**.

### Generated constant indexed packed targets — 2026-10-23

Indexed packed part-select targets whose genvar arithmetic is resolved during
legacy elaboration now normalize to fixed vector windows. Both `IndexedUp` and
`IndexedDown` preserve the elaborated base label and direction; runtime or
out-of-range indexed selections remain loud. The `generate_indexed_targets`
fixture and differential row cover both directions in generated assignments.
The 22,046-file census moves **4,645 → 4,649 clean** and **17,335 → 17,331
partial**; `AssignmentExpression:target` falls **3,500 → 3,496**.
Differential coverage is **63 rows, 59 matches, 0 disagreements, and 4
recorded refusals**; grammar coverage remains **203 witnesses, 72 MATCH, and
131 REFUSE**.

### Constant-range right-streaming `with` targets — 2026-10-23

An unsized right-streaming assignment with a constant simple `with [left:right]`
range now expands only the selected cells of a fixed unpacked integral array.
The unselected cells retain their prior values; dynamic, reversed, partial
multidimensional, and aggregate ranges remain loud. The `streaming_with_range`
fixture and differential row cover the selected-prefix form. The 22,046-file
census moves **4,653 → 4,654 clean** and **17,327 → 17,326 partial**;
`AssignmentExpression:target` falls **3,492 → 3,491**. Differential coverage
is **66 rows, 62 matches, 0 disagreements, and 4 recorded refusals**; grammar
coverage is **204 witnesses, 73 MATCH, and 131 REFUSE**.

## Constant-size dynamic arrays copied to fixed arrays — 2026-10-23

A 2-state dynamic array whose single allocation is a constant `new[N]` now
uses the existing flat vector-cell representation. The declaration materializes
zero-based cells, a procedural `dynamic = new[N]` allocation is retained as an
empty state transition, dynamic element reads and writes reuse the guarded
finite-cell lowering, and equal-length fixed-array copies preserve declaration
order. Four-state arrays, uninitialized or repeated allocations, nonconstant
sizes, and size-mismatched fixed targets remain loud; no runtime resize model is
implied. The `dynamic_fixed_array_copy` fixture and differential row exercise
both declaration and procedural allocation shapes.

The fresh 22,046-file census moves **4,654 → 4,656 clean** and **17,326 →
17,324 partial**; `AssignmentExpression:target` falls **3,491 → 3,464**.
Differential coverage moves **66/62/0/4 → 67/63/0/4** (rows/agree/disagree/
recorded refusals), and the grammar census moves **204/73/131 → 206/75/131**.

## Pure `$strobe` arguments — 2026-10-23

`$strobe` now accepts pure converted scalar expressions as deferred arguments.
The self-check evaluator already queues the call for the postponed end of the
time-zero slot, so a later blocking assignment is observed exactly by the
strobe. Effectful, aggregate, and otherwise unsupported arguments remain loud;
no general postponed scheduler is introduced. The `strobe_dynamic` fixture and
differential row cover the final-value behavior.

The fresh 22,046-file census moves **4,656 → 4,678 clean** and **17,324 →
17,302 partial**. `ExpressionStatement:CallExpression` falls **3,476 →
3,451** files while `AssignmentExpression:target` remains **3,464**.
Differential coverage moves **67/63/0/4 → 68/64/0/4** and grammar coverage
remains **206/75/131**.

## Constant indexed writes to sampled dynamic arrays — 2026-10-23

A dynamic array with one constant `new[N]` allocation now flattens into the
existing zero-based vector-cell state. Constant element writes and reads in
procedural contexts update those cells, including local declarations whose
allocation is sampled from the enclosing initial block. Nonconstant or repeated
allocation, resizing, aggregate operations, associative and real indices, and
continuous assignments to dynamic elements remain loud.

The fresh 22,046-file census moves **4,678 → 4,679 clean** and **17,302 →
17,301 partial**. `AssignmentExpression:target` falls **3,464 → 3,441** files
and `MemberAccessExpression` falls **1,025 → 1,022**. Differential coverage
moves **68/64/0/4 → 69/65/0/4**; grammar coverage remains **206/75/131**.

## Literal `$timeunit` and `$timeprecision` queries — 2026-10-23

System functions `$timeunit` and `$timeprecision` now fold when the source has a
literal `` `timescale 1<unit>/1<precision> `` directive. The result is the
signed IEEE time exponent (for example, `1ns/1ps` gives `-9` and `-12`), so the
existing integral evaluator handles assignments and comparisons without a
scheduler. Missing, malformed, or nonliteral scale metadata remains loud.
The `time_scale_query` fixture and differential row cover both queries.

The fresh 22,046-file census moves **4,679 → 4,684 clean** and **17,301 →
17,296 partial**. `CallExpression` falls **3,292 → 3,283** files; the two
assignment and expression-statement leaders are unchanged. Differential
coverage moves **69/65/0/4 → 70/66/0/4** and grammar coverage remains
**206/75/131**.

## Inert literal `$sdf_annotate` calls — 2026-10-23

The self-check tier now erases `$sdf_annotate` when its only argument is a
literal SDF filename, or when the three-argument spelling supplies a literal
module scope and the explicitly empty `config_file`. These forms have no
timing annotation to apply in the time-zero state. Calls with dynamic
filenames, nonempty configuration, or other optional arguments remain loud;
this does not introduce an SDF timing model.

The `sdf_annotate` fixture and differential row cover both admitted forms. The
fresh 22,046-file census moves **4,684 → 4,689 clean** and **17,296 → 17,291
partial**; `ExpressionStatement:CallExpression` falls **3,451 → 3,419** and
`AssignmentExpression:target` becomes the leading blocker at 3,441.
Differential coverage moves **70/66/0/4 → 71/67/0/4** and grammar coverage
remains **206/75/131**.

## Pure real and shortreal literal writes — 2026-10-24

Blocking assignments of a signed or unsigned real/shortreal literal now erase
through the opaque floating-storage boundary. Unary plus/minus and the
frontend's literal conversion shell are included; nonblocking, timed,
computed, named, and read-dependent writes remain loud because the tier has no
floating state representation.

The `floating_literal_write` fixture and differential row cover the admitted
form, with extractor regressions for literal and nonliteral RHS values. The
fresh 22,046-file census moves **4,689 → 4,705 clean** and **17,291 → 17,275
partial**; `AssignmentExpression:target` falls **3,441 → 3,321**. Differential
coverage moves **71/67/0/4 → 72/68/0/4** and grammar coverage moves
**206/75/131 → 207/76/131**.

## Empty zero-argument subroutine calls — 2026-10-24

Calls to a task or void function whose declaration has no formals and an
actually empty statement list now erase in statement position. Their
declarations are metadata only, and the call has no state, timing, or output
effect. Any formal argument, defaulted signature, nonempty body, or other
subroutine behavior remains loud.

The `empty_subroutine_call` fixture and differential row cover both an empty
task and an empty function; focused extractor tests pin the loud boundaries.
The fresh 22,046-file census moves **4,705 → 4,721 clean** and **17,275 →
17,259 partial**; `ExpressionStatement:CallExpression` falls **3,419 →
3,040**, and `SubroutineSymbol:Subroutine` falls **1,715 → 1,665**.
Differential coverage moves **72/68/0/4 → 73/69/0/4**; grammar coverage moves
**207/76/131 → 209/78/131**.

## Opaque uninitialized class-handle declarations — 2026-10-24

Uninitialized class-handle declarations, including built-in handles such as
`mailbox`, now disappear as declaration metadata in both module and procedural
scopes. The default null handle has no flat self-check slot; construction,
assignments, reads, and method calls remain loud and no object model is added.

The `opaque_handle_decl` fixture and differential row cover module and local
declarations, with extractor regressions for initialized and read handles. The
fresh 22,046-file census moves **4,721 → 4,722 clean** and **17,259 → 17,258
partial**; `VariableSymbol:2state` falls **3,383 → 2,376**. Differential
coverage moves **73/69/0/4 → 74/70/0/4**; grammar coverage remains
**209/78/131**.

## Direct null writes to opaque class handles — 2026-10-24

A blocking assignment of the literal `null` to a named class-handle variable
now erases through the opaque-storage boundary. Member receivers, selected
targets, nonblocking or timed assignments, construction, and all other handle
operations remain loud; no object or alias state is introduced.

The `opaque_handle_null_write` fixture and differential row cover the admitted
form, with extractor regressions for nonblocking writes and handle reads. The
fresh 22,046-file census keeps **4,722 clean / 17,258 partial** and lowers
`AssignmentExpression:target` **3,321 → 3,313**. Differential coverage moves
**74/70/0/4 → 75/71/0/4**; grammar coverage remains **209/78/131**.

## Empty function default values — 2026-10-24

An empty zero-argument function call in expression position now yields the
declared return type's standard default: all zero bits for a 2-state return and
all X bits for a 4-state return. The empty declaration remains metadata only;
formal arguments, nonempty bodies, and unsupported return types stay loud.

The `empty_function_value` fixture and differential row cover both defaults,
with extractor regressions checking their bit patterns. The fresh 22,046-file
census moves **4,722 → 4,745 clean** and **17,258 → 17,235 partial**;
`CallExpression` falls **3,283 → 3,100**. Differential coverage moves
**75/71/0/4 → 76/72/0/4**; grammar coverage remains **209/78/131**.

## Bare assertion-control tasks — 2026-10-24

Bare `$asserton`, `$assertoff`, and `$assertkill` statement tasks now erase in
the self-check tier. The tier has no concurrent-assertion state for these
controls to change, so scoped and argumented forms remain loud rather than
inventing assertion scheduling or state. The `assert_control` fixture and
differential row cover all three admitted tasks and the argumented refusal.

The fresh 22,046-file census moves **4,745 → 4,746 clean** and **17,235 →
17,234 partial**; `ExpressionStatement:CallExpression` falls **3,040 →
3,019**. Differential coverage moves **76/72/0/4 → 77/73/0/4** (rows/agree/
disagree/recorded refusals), and grammar coverage remains **209/78/131**.

## Opaque unbounded mailbox construction writes — 2026-10-24

An exact bare `new()` assigned to a built-in `mailbox` handle now erases as an
opaque-storage write. The flat self-check state has no mailbox object or handle
slot, so this admits the declaration-plus-construction shape without
fabricating an object. Explicit `new(0)`, bounded or otherwise argumented
constructors, user classes, and every mailbox read or method call remain loud.
The `opaque_mailbox_new_write` fixture and differential row cover the admitted
form; extractor tests pin the explicit-zero boundary.

The fresh 22,046-file census moves **4,746 → 4,747 clean** and **17,234 →
17,233 partial**; `AssignmentExpression:target` falls **3,313 → 3,219**.
Differential coverage moves **77/73/0/4 → 78/74/0/4**, and grammar coverage
moves **209/78/131 → 210/79/131**.

## Opaque zero-key semaphore construction writes — 2026-10-24

An exact `semaphore` handle assignment of the literal `new(0)` now erases as
an opaque-storage write. A zero-key semaphore has no represented object state
in the self-check tier, while nonzero constructors and all `get`, `put`, or
other synchronization operations remain loud. The
`opaque_semaphore_zero_write` fixture and differential row cover the admitted
form; extractor tests pin the nonzero boundary.

The fresh 22,046-file census keeps **4,747 clean / 17,233 partial** and lowers
`AssignmentExpression:target` **3,219 → 3,193**. Differential coverage moves
**78/74/0/4 → 79/75/0/4**, and grammar coverage remains **210/79/131**.

## Time-zero `$realtime` writes to opaque real storage — 2026-10-24

A blocking assignment of the zero-argument `$realtime` query to real or
shortreal storage now erases in the time-zero self-check slice. The query has
no modeled state effect and floating storage is already opaque; integer
targets, nonblocking or timed writes, and later real reads remain loud. The
`realtime_write` fixture and differential row cover the admitted form, with
extractor tests pinning the nonblocking boundary.

The fresh 22,046-file census keeps **4,747 clean / 17,233 partial** and lowers
`AssignmentExpression:target` **3,193 → 3,155**. Differential coverage moves
**79/75/0/4 → 80/76/0/4**, and grammar coverage remains **210/79/131**.

## Literal-only string concatenation writes — 2026-10-24

A blocking assignment of a concatenation made entirely from string literals
to a named `string` variable now erases through the existing opaque string
storage boundary. Dynamic operands, replication, nonblocking or timed forms,
and later string reads remain loud because the tier carries no string state.
The `string_concat_write` fixture and differential row cover the admitted form,
with extractor tests pinning the dynamic and nonblocking boundaries.

The fresh 22,046-file census keeps **4,747 clean / 17,233 partial** and lowers
`AssignmentExpression:target` **3,155 → 3,153**. Differential coverage moves
**80/76/0/4 → 81/77/0/4**, and grammar coverage remains **210/79/131**.

## Constant string-literal replication writes — 2026-10-24

A blocking assignment of a nonnegative constant replication containing only
string literals to a named `string` variable now erases through the opaque
string boundary. Dynamic replication counts, nonliteral operands, replication
of a variable, nonblocking or timed forms, and later string reads remain loud.
The `string_replication_write` fixture and differential row cover the admitted
form, with extractor tests pinning the dynamic and nonblocking boundaries.

The 22,046-file census is unchanged at **4,747 clean / 17,233 partial** and
`AssignmentExpression:target` remains **3,153**; this syntax family is absent
from the remaining blocker records. Differential coverage moves
**81/77/0/4 → 82/78/0/4**, and grammar coverage remains **210/79/131**.

## Empty queue literal writes — 2026-10-24

A blocking assignment of the empty queue literal to a named queue now erases
through the flat self-check boundary, which has no queue object state. Nonempty
queue literals, nonblocking or timed forms, and queue reads or methods remain
loud. The `empty_queue_write` fixture and differential row cover the admitted
form, with extractor tests pinning nonempty and nonblocking boundaries.

The fresh 22,046-file census keeps **4,747 clean / 17,233 partial** and lowers
`AssignmentExpression:target` **3,153 → 3,145**. Differential coverage moves
**82/78/0/4 → 83/79/0/4**, and grammar coverage moves
**210/79/131 → 211/80/131** with the empty-queue witness.

## Empty dynamic-array literal writes — 2026-10-24

A blocking assignment of a zero-item literal to a named dynamic array now
erases through the flat self-check boundary, which has no dynamic-array object
state. Nonempty values, nonblocking or timed forms, and later size or element
reads remain loud. The `empty_dynamic_array_write` fixture and differential row
cover the admitted form, with extractor tests pinning the publication and
nonempty boundaries.

The fresh 22,046-file census keeps **4,747 clean / 17,233 partial** and lowers
`AssignmentExpression:target` **3,145 → 3,144**. Differential coverage moves
**83/79/0/4 → 84/80/0/4**; grammar coverage remains **211/80/131**.

## Direct null writes to opaque chandles — 2026-10-24

A blocking assignment of `null` to a named `chandle` now erases through the
opaque-handle boundary. Selected targets, nonblocking or timed forms, and
chandle reads, comparisons, and calls remain loud. The
`opaque_chandle_null_write` fixture and differential row cover the admitted
form, with extractor tests pinning the nonblocking boundary.

The fresh 22,046-file census keeps **4,747 clean / 17,233 partial** and lowers
`AssignmentExpression:target` **3,144 → 3,139**. Differential coverage moves
**84/80/0/4 → 85/81/0/4**, and grammar coverage remains **211/80/131**.

## Direct null writes to opaque virtual interfaces — 2026-10-24

A blocking assignment of `null` to a named virtual-interface handle now erases
through the opaque-handle boundary. Selected targets, nonblocking or timed
forms, and virtual-interface reads, comparisons, and calls remain loud. The
`opaque_virtual_interface_null_write` fixture and differential row cover the
admitted form, with extractor tests pinning the null-write boundary.

The 22,046-file census remains **4,747 clean / 17,233 partial** with
`AssignmentExpression:target` at **3,139**; no remaining corpus record has
this isolated target shape. Differential coverage moves **85/81/0/4 →
86/82/0/4**, and grammar coverage remains **211/80/131**.

## Direct null writes to opaque events — 2026-10-24

A blocking assignment of `null` to a named event handle now erases through
the opaque-handle boundary. Selected targets, nonblocking or timed forms, and
event triggers, waits, reads, or comparisons remain loud. The
`opaque_event_null_write` fixture and differential row cover the admitted form,
with extractor tests pinning the nonblocking boundary.

The fresh 22,046-file census keeps **4,747 clean / 17,233 partial** and lowers
`AssignmentExpression:target` **3,139 → 3,133**. Differential coverage moves
**86/82/0/4 → 87/83/0/4**, and grammar coverage remains **211/80/131**.

## Direct `process::self()` writes to opaque process handles — 2026-10-24

A blocking assignment of `process::self()` to a named process handle now
erases through the opaque-handle boundary. Nonblocking or timed forms,
process status and method reads, and other process operations remain outside
this write admission; the tier does not invent process identity or scheduling
state.

The `opaque_process_self_write` fixture and differential row cover the
admitted form, with extractor tests pinning the nonblocking boundary. The
fresh 22,046-file census moves **4,747 → 4,750 clean** and **17,233 → 17,230
partial**; `AssignmentExpression:target` falls **3,133 → 3,106**.
Differential coverage moves **87/83/0/4 → 88/84/0/4**, and grammar coverage
remains **211/80/131**.

## Post-incremented fixed-array index writes — 2026-10-24

Assignments through a one-dimensional fixed-array index of the form
`array[index++] = value` now lower to a bounded cell choice followed by the
post-increment update. The old index is sampled for the write, and the update
is retained even when the index is outside the represented cells. Pre-
increment, dynamic storage, and effectful selectors outside this exact form
remain loud.

The `postincrement_array_target` fixture and differential row cover the
admitted order, with extractor tests checking that the index update follows
the conditional cell write. The fresh 22,046-file census moves **4,750 →
4,752 clean** and **17,230 → 17,228 partial**; `AssignmentExpression:target`
falls **3,106 → 3,103**. Differential coverage moves **88/84/0/4 →
89/85/0/4**, and grammar coverage remains **211/80/131**.

## Pure real system-function writes — 2026-10-24

Blocking writes of side-effect-free IEEE real math and conversion calls to a
named `real` or `shortreal` now erase through the opaque floating-storage
boundary. The admitted calls include the standard arithmetic, transcendental,
rounding, and real-conversion system functions; every argument is checked for
literal/read-only/pure-operator structure. Nonblocking or timed writes,
effectful operands, and subsequent real observations remain outside this
admission.

The `floating_math_write` fixture and differential row cover the admitted
form, with extractor tests pinning an incrementing operand. The fresh
22,046-file census keeps **4,752 clean / 17,228 partial** and lowers
`AssignmentExpression:target` **3,103 → 3,049**; `CallExpression` is now the
largest blocker at **3,100**. Differential coverage moves **89/85/0/4 →
90/86/0/4**, and grammar coverage remains **211/80/131**.

## Time-zero `$stime` queries — 2026-10-24

The zero-argument `$stime` system function now lowers to a 32-bit zero literal
in the time-zero self-check slice. Argumented queries remain loud, while the
existing `$time` admission is unchanged; no clock or scheduler state is
introduced.

The `stime_query` fixture and differential row cover assignment and comparison
of the query, with extractor tests pinning the argument boundary. The fresh
22,046-file census moves **4,752 → 4,761 clean** and **17,228 → 17,219
partial**; `CallExpression` falls **3,100 → 3,088** and remains the largest
blocker. Differential coverage moves **90/86/0/4 → 91/87/0/4**, and grammar
coverage remains **211/80/131**.

## Integral conversions of time-zero `$realtime` — 2026-10-24

When a zero-argument `$realtime` query is elaborated in an integral conversion
context, the self-check extractor lowers it to a zero literal carrying the
existing `time_zero` provenance. This is the exact value at time zero; direct
real-valued uses, argumented queries, and conversions outside the integral
surface remain loud, so no real storage or elapsed-time state is fabricated.

The `realtime_integral_query` fixture and differential row cover the admitted
assignment and comparison. Extractor tests pin both the zero-width result and
the direct real-valued refusal. The fresh 22,046-file census moves **4,761 →
4,762 clean** and **17,219 → 17,218 partial**; `CallExpression` falls **3,088
→ 3,087**. Differential coverage moves **91/87/0/4 → 92/88/0/4**, and grammar
coverage remains **211/80/131**.

## Zero-size queue and dynamic-array queries — 2026-10-24

An uninitialized queue or dynamic array has size zero. The self-check extractor
now lowers its `.size()` query to a 32-bit zero literal when the receiver has no
initializer and every source occurrence is the same read-only size query. This
keeps aggregate storage, pushes, assignments, and other methods outside the
tier; initialized or mutated receivers remain loud.

The `zero_size_query` fixture and differential row cover both aggregate kinds,
and extractor tests pin the mutation and initializer boundaries. The fresh
22,046-file census moves **4,762 → 4,766 clean** and **17,218 → 17,214
partial**; `CallExpression` falls **3,087 → 3,083**. Differential coverage
moves **92/88/0/4 → 93/89/0/4**, and grammar coverage remains **211/80/131**.

## Zero-length queries on inert strings — 2026-10-24

An uninitialized `string` has length zero, so its `.len()` query now lowers to
a 32-bit zero literal when every receiver occurrence is that same read-only
query. String writes, initializers, and other methods remain loud because the
self-check state does not model string contents.

The `zero_string_len` fixture and differential row cover the admitted query,
with extractor tests pinning the written-string boundary. The fresh 22,046-file
census remains **4,766 clean / 17,214 partial** and `CallExpression` remains
**3,083**; this slice changes the differential table **93/89/0/4 → 94/90/0/4**
while grammar coverage remains **211/80/131**.

## Zero-size queries after explicit empty writes — 2026-10-24

Explicit writes of `{}` to an inert queue or dynamic array, and `""` to an
inert string, now preserve the corresponding zero `.size()` or `.len()` result.
The source-use guard still rejects any later push, nonempty write, initializer,
or other aggregate/string observation, so this extends the empty-state rule
without introducing storage.

The `zero_size_after_empty_write` fixture and differential row cover all three
forms, with extractor tests pinning the nonempty mutation boundary. The fresh
22,046-file census moves **4,766 → 4,772 clean** and **17,214 → 17,208
partial**; `CallExpression` falls **3,083 → 3,077**. Differential coverage
moves **94/90/0/4 → 95/91/0/4**, and grammar coverage remains **211/80/131**.

## Zero-size dynamic-array allocation queries — 2026-10-24

A dynamic array assigned `new[0]` is empty by definition. The self-check
extractor now erases that allocation and lowers its following `.size()` query
to zero; positive allocations, initialized arrays, and later mutations remain
loud. This reuses the existing no-storage boundary for empty arrays.

The `zero_size_after_new_zero` fixture and differential row cover the admitted
form, with extractor tests pinning the positive-allocation boundary. The fresh
22,046-file census moves **4,772 → 4,775 clean** and **17,208 → 17,205
partial**; `CallExpression` falls **3,077 → 3,074** and
`AssignmentExpression:target` falls **3,049 → 3,046**. Differential coverage
moves **95/91/0/4 → 96/92/0/4**, and grammar coverage remains **211/80/131**.

## Zero-argument literal-return function calls — 2026-10-24

A zero-argument function whose complete body is one integral literal return is
now lowered at each call site to that already-sized literal. The declaration is
metadata-only, matching the existing empty-function treatment. Arguments,
named-value reads, nested calls, operators, and multi-statement bodies remain
loud so the extractor never erases runtime state or evaluation order.

The `literal_function_return` fixture and differential row cover the admitted
call, with extractor tests pinning effectful and nonliteral boundaries. The
fresh 22,046-file census moves **4,775 → 4,783 clean** and **17,205 → 17,197
partial**; `CallExpression` falls **3,074 → 2,997** and
`SubroutineSymbol:Subroutine` falls **1,665 → 1,636**. Differential coverage
moves **96/92/0/4 → 97/93/0/4**, and grammar coverage remains **211/80/131**.

## Literal-input literal-return function calls — 2026-10-24

A function whose complete body returns one integral literal may now be called
with integral literal input arguments. Input formals are metadata only, so the
call lowers to the already-sized return literal and the existing self-check
interpreter evaluates it without creating a callable frame. Output, inout, and
reference formals, dynamic or effectful arguments, named-value reads, nested
calls, operators, and multi-statement bodies remain loud because they can
observe or update caller state.

The `literal_function_argument` fixture and differential row cover the value
path, while focused extractor tests also pin discarded results and the dynamic
and copy-out boundaries. The current 22,048-path census moves **4,816 → 4,817
clean** and **17,166 → 17,165 partial / 66 include skips**;
`SubroutineSymbol:Subroutine` falls **1,636 → 1,634** while the leading call
blockers remain unchanged. Differential coverage moves **122/118/0/4 →
123/119/0/4**; the grammar census remains **214/83/131**.

## Source-ordered pure static dependencies — 2026-10-27

Static locals preserve source order within each procedural scope. A later
initializer may read an earlier static declaration when the existing
closed-pure checks pass, and the hoisted `Var` declarations retain that order.
Runtime, effectful, random, environment, cross-scope, and pre-process module
initializers remain loud. The `static_dependency_initializer` fixture and
extractor lifetime tests cover the admitted dependency and the retained
barrier.

The differential matrix grows **330/324/0/6 → 331/325/0/6**, with grammar
coverage unchanged at **218/97/121**. The chapter-only census moves
**5,331 clean / 16,667 partial → 5,359 clean / 16,639 partial** over 22,065
files with 67 include skips; `StaticLocal:initializer` falls **168 → 140**.

## Named literal-history literal-return function calls — 2026-10-27

A function whose complete body returns one integral literal may now receive a
named integral argument when source order proves that the declaration and all
earlier writes are direct blocking literals in the time-zero initial history.
The argument is still checked for source purity before the already-sized return
literal is materialized, so no callable frame or input storage is introduced.
Computed, control-dependent, timed, nonblocking, dynamic, output, inout, and
reference arguments remain loud. The `literal_function_named_history` fixture
and differential row cover two successive literal writes and two call sites;
focused extractor tests cover the computed-history refusal.

The chapter-only census remains **5,331 clean / 16,667 partial** over 22,065
files with 67 include skips; its leading call blockers are unchanged because
the fixture is a repository witness outside the corpus walk. Differential
coverage grows **329/323/0/6 → 330/324/0/6**, with grammar coverage unchanged
at **218/97/121**.

## Inert monitor toggles without registrations — 2026-10-24

No-argument `$monitoron` and `$monitoroff` calls now lower to inert diagnostic
nodes when the design contains no `$monitor` registration. Argumented controls
and any design that registers a monitor remain loud because monitor output and
its enable state are outside the self-check state.

The `monitor_controls` fixture and differential row cover both semicolon and
parenthesized no-argument spellings, with extractor tests pinning registration
and argument boundaries. The 22,046-file census remains **4,783 clean / 17,197
partial**; its blocker counts are unchanged. Differential coverage moves
**97/93/0/4 → 98/94/0/4**, and grammar coverage remains **211/80/131**.

## Literal-initialized procedural floating declarations — 2026-10-24

Procedural `real` and `shortreal` declarations initialized by a pure numeric
literal now lower to inert metadata. The flat self-check state has no floating
slot, and a literal initializer has no effect beyond creating that unavailable
value; reads, effectful initializers, writes, arithmetic, and formatting remain
loud. The `literal_real_decl` fixture and differential row cover signed real
and shortreal literals, while extractor tests retain the dynamic initializer
boundary.

The current 22,048-path census keeps **4,784 clean** and moves **17,196 →
17,198 partial** because this corpus snapshot contains two additional paths;
`VariableSymbol:2state` falls **2,376 → 2,351**. Differential coverage moves
**102/98/0/4 → 103/99/0/4**, and grammar coverage moves **211/80/131 →
212/81/131**.

## Standard-output `$fwrite` — 2026-10-24

`$fwrite` to the predefined standard-output descriptor now lowers to the
existing no-newline `$write` node. Literal formats and the existing pure
expression arguments are retained; other descriptors and dynamic formats stay
loud because external file state is not represented.

The `fwrite_stdout` fixture and differential row cover the descriptor and
newline behavior, with extractor tests pinning nonstandard descriptors. The
22,046-file census remains **4,783 clean / 17,197 partial** with unchanged
blocker counts. Differential coverage moves **98/94/0/4 → 99/95/0/4**, and
grammar coverage remains **211/80/131**.

## Constant-indexed right-streaming `with` targets — 2026-10-24

An unsized right-streaming assignment with a constant indexed `with [base +:
width]` or `[base -: width]` range now expands the corresponding cells of an
ascending fixed unpacked integral array. The indexed-down form starts at
`base-width+1`, matching the array's forward stream order; bounds, dynamic
expressions, descending declarations, partial arrays, and aggregate operands
remain loud. The `streaming_indexed_with_range` fixture checks both directions
and preserves every unselected cell. The 22,046-file corpus remains **4,783
clean / 17,197 partial / 66 include skips** because its indexed `with` cases
use dynamic arrays. Differential coverage moves **99/95/0/4 → 100/96/0/4**;
grammar coverage remains **211 witnesses, 80 MATCH, and 131 REFUSE**.

## Discarded zero-argument literal-return calls — 2026-10-24

A statement-position call to a zero-argument user function whose complete body
is one integral literal `return` now erases the discarded result. Calls with
arguments, named-value reads, operators, nested calls, or multi-statement
bodies remain loud; no callable frame or state model is introduced. The
`literal_function_statement` fixture and differential row cover the admitted
shape. The 22,046-file corpus remains **4,783 clean / 17,197 partial / 66
include skips** with unchanged blocker counts. Differential coverage moves
**100/96/0/4 → 101/97/0/4**; grammar coverage remains **211 witnesses, 80
MATCH, and 131 REFUSE**.

## Inert literal `$timeformat` calls — 2026-10-24

Literal `$timeformat` calls with no `%t` consumer now erase as inert
configuration in the self-check surface, which has no time-format renderer.
Dynamic arguments and any source containing a `%t` consumer remain loud. The
`timeformat_inert` fixture and differential row cover the restricted call. The
22,046-file corpus moves **4,783 → 4,784 clean** and **17,197 → 17,196
partial**, with `ExpressionStatement:CallExpression` falling **3,019 → 3,017**
and 66 include skips. Differential coverage moves **101/97/0/4 →
102/98/0/4**; grammar coverage remains **211 witnesses, 80 MATCH, and 131
REFUSE**.

## Literal string length queries — 2026-10-24

The self-check extractor now lowers `.len()` on an unchanged pure string
literal to its exact integral character count. The string itself remains
opaque: writes, dynamic initializers, non-ASCII contents, and other string
methods remain loud. The `literal_string_len` fixture and extractor tests cover
nonempty and empty literals plus the write-before-query boundary.

The 22,048-path census moves **4,784 → 4,791 clean** and **17,198 → 17,191
partial**; `CallExpression` falls **2,997 → 2,990**. Differential coverage
moves **103/99/0/4 → 104/100/0/4**, while grammar coverage remains
**212/81/131**.

## Literal string `getc` queries — 2026-10-24

An unchanged pure ASCII string literal now exposes its exact `.getc(index)` byte
as an integral scalar. Negative and out-of-range indices lower to the standard's
zero byte; in-range indices lower to the corresponding ASCII value. Writes,
dynamic indices, dynamic or non-ASCII strings, and other string methods remain
loud because the self-check state has no mutable string storage. The
`literal_string_getc` fixture and extractor tests cover the byte and zero-bound
cases plus the dynamic, write, and encoding boundaries.

The 22,048-path census moves **4,791 → 4,797 clean** and **17,191 → 17,185
partial**; `CallExpression` falls **2,990 → 2,986**. Differential coverage
moves **104/100/0/4 → 105/101/0/4**, while grammar coverage remains
**212/81/131**.

## Single literal continuous net drivers — 2026-10-24

A single whole-net continuous assignment whose RHS is a pure integral literal
now lowers to the existing time-zero blocking assignment. With no future RHS
change, no second driver, and no selected target, this is the exact value seen
by the initial-only self-check runner without adding a continuous-driver queue
or resolution rule. Dynamic RHS expressions, variable targets, selected
targets, and multiple drivers remain loud. `constant_net_driver` supplies the
differential row and extractor boundary tests.

The corpus census is unchanged by this focused witness: the current target-only
continuous-driver files all require dynamic or multiple-driver behavior. The
differential table moves **105/101/0/4 → 106/102/0/4**; grammar coverage moves
**212/81/131 → 213/82/131** because the new fixture changes the retained
syntax-kind witness.

## Type-keyed enum defaults in packed-struct array targets — 2026-10-24

The fixed-array assignment-pattern rung now admits a narrow packed-struct
case: a whole fixed unpacked array may use one enum type key and a literal
scalar default. Extraction normalizes pyslang's nested pattern inventory to
literal field values and lowers the write through the existing flat cell
representation. Dynamic/effectful keys or defaults and unsupported aggregate
shapes remain loud. `typed_default_array_pattern` is the differential witness.

The 22,048-path census moves **4,797 → 4,798 clean** and **17,185 → 17,184
partial**; `AssignmentExpression:target` falls **3,046 → 3,045**. Differential
coverage moves **106/102/0/4 → 107/103/0/4**; grammar coverage remains
**213/82/131**.

## Single literal continuous packed-bit drivers — 2026-10-24

The continuous-driver rung now admits one constant packed bit or part-select
with a pure integral literal RHS. Extraction lowers it to the existing
selected blocking assignment at time zero, with no driver queue or resolution
choice. Multiple drivers, dynamic RHS/selections, and aggregate or streaming
targets remain loud. `constant_net_bit_driver` supplies the differential row.

The 22,048-path census is unchanged at **4,798 clean / 17,184 partial / 66
include skips** and `AssignmentExpression:target` remains **3,045 files**.
Differential coverage moves **107/103/0/4 → 108/104/0/4**; grammar coverage
remains **213/82/131**.

## Static literal wire-driver resolution — 2026-10-24

The continuous-driver rung now resolves multiple whole-net literal drivers on
declared wires at time zero, per bit, using the IEEE `z`/equal/conflict/`x`
table. The result is lowered to one flat assignment; no live driver queue or
strength model is introduced. Dynamic or variable drivers, selected windows,
and future source changes remain loud. `static_net_resolution` supplies the
differential row.

The 22,048-path census moves **4,798 → 4,806 clean** and **17,184 → 17,176
partial**; `AssignmentExpression:target` falls **3,045 → 3,037**. Differential
coverage moves **108/104/0/4 → 109/105/0/4**; grammar coverage remains
**213/82/131**.

## Literal continuous fixed-array variable cells — 2026-10-24

A pure integral literal continuous assignment to one constant cell of a
one-dimensional fixed-unpacked variable now lowers to the existing time-zero
blocking write for that expanded scalar cell. The source cell must occur once;
net arrays, dynamic or effectful indices, nonliteral sources, and multiple
drivers stay on the continuous-driver boundary. The
`constant_array_cell_driver` fixture supplies the differential evidence and
reuses the ordinary cell storage and interpreter path. The corpus census is
unchanged because its fixed-array continuous rows either use net-array types or
dynamic drivers; differential coverage moves **109/105/0/4 → 110/106/0/4**.

## Literal continuous fixed-array net cells — 2026-10-24

A one-dimensional fixed-unpacked `wire` array with one pure integral literal
driver per constant cell now lowers to independent flat `Net` cells. The
existing time-zero write and literal net-resolution paths are reused; whole,
dynamic, multidimensional, non-integral, and effectful forms remain loud.
`constant_net_array_cell_driver` supplies the differential evidence.

The 22,048-path census moves **4,806 → 4,810 clean** and **17,176 → 17,172
partial**; `AssignmentExpression:target` remains **3,037** because the
remaining target-only rows use dynamic or aggregate shapes. Differential
coverage moves **113/109/0/4 → 114/110/0/4**; grammar coverage remains
**213/82/131**.

## Literal continuous packed-variable drivers — 2026-10-24

A pure integral literal continuous assignment to one whole packed variable or
one constant packed bit/part-select now lowers to the existing time-zero
blocking write. The source target must occur once; dynamic or effectful
sources/selections and multiple drivers remain loud because they need a live
continuous-driver path. `constant_variable_driver` covers both target forms.
The corpus census remains **4,806 clean / 17,176 partial / 66 include skips**
with `AssignmentExpression:target` at **3,037 files**; differential coverage
moves **110/106/0/4 → 111/107/0/4**.

## Disjoint literal continuous packed-net windows — 2026-10-24

Multiple continuous assignments to disjoint constant bit/part-select windows
of one packed wire now lower independently to time-zero blocking writes when
all sources are pure integral literals. Overlapping windows and any dynamic
peer remain loud because they require per-bit net resolution and live driver
updates. `disjoint_literal_net_windows` supplies the differential witness.
The corpus census remains **4,806 clean / 17,176 partial / 66 include skips**
with `AssignmentExpression:target` at **3,037 files**; differential coverage
moves **111/107/0/4 → 112/108/0/4**.

## Static literal continuous packed-window resolution — 2026-10-24

The selected-window lowering now resolves overlapping literal drivers on one
packed wire per bit with the IEEE `z`/equal/conflict/`x` table. Dynamic peers,
out-of-range windows, strengths, and future source changes remain loud because
they need live driver and resolution state. `overlapping_literal_net_windows`
supplies the conflict and unchanged-bit witness. The corpus census remains
**4,806 clean / 17,176 partial / 66 include skips**, with
`AssignmentExpression:target` at **3,037 files**; differential coverage moves
**112/108/0/4 → 113/109/0/4**.

## Literal continuous `tri` drivers — 2026-10-24

A scalar or packed `tri` with only pure integral literal continuous drivers
now uses the same fixed four-state result as a literal `wire`. The declaration
remains a net and the existing per-bit resolution handles `z`, equal values,
conflicts, and `x`; dynamic, effectful, strength, delayed, and future-update
forms remain loud. `constant_tri_driver` supplies the differential evidence.

The census remains **4,810 clean / 17,172 partial / 66 include skips** with
`AssignmentExpression:target` at **3,037 files**. Differential coverage moves
**114/110/0/4 → 115/111/0/4**; grammar coverage remains **213/82/131**.

## Explicit-strength literal continuous drivers — 2026-10-24

A single whole-net continuous driver with an explicit `(strength1, strength0)`
pair now lowers when its source is a pure integral literal. The fixed value
uses the existing time-zero assignment path; selected targets, multiple
strength drivers, dynamic or effectful sources, and multiple or mixed-strength
`tri` drivers stay loud until per-driver strength state is represented.
`constant_strength_driver` supplies the differential witness.

The census remains **4,810 clean / 17,172 partial / 66 include skips**, while
`AssignmentExpression:target` falls **3,037 → 3,036**. Differential coverage
moves **115/111/0/4 → 116/112/0/4**; grammar coverage moves
**213/82/131 → 214/83/131**.

## Single strengthened `tri` literal drivers — 2026-10-24

A `tri` with one explicitly strengthened whole-net driver and a pure integral
literal source now reuses the fixed time-zero value path. With no competing
driver, the strength cannot change the resolved value, so this case requires
no per-driver state. Selected targets, multiple or mixed-strength drivers,
dynamic/effectful sources, and delayed assignments remain loud.
`constant_tri_strength_driver` supplies the differential witness.

The census remains **4,810 clean / 17,172 partial / 66 include skips**, with
`AssignmentExpression:target` unchanged at **3,036 files**. Differential
coverage moves **116/112/0/4 → 117/113/0/4**; grammar coverage remains
**214/83/131**.

## Single strengthened packed-select drivers — 2026-10-24

A single explicitly strengthened packed bit or constant part-select with a
pure integral literal source now lowers to the existing selected time-zero
write. Multiple strengthened selected drivers, dynamic/effectful sources, and
aggregate targets remain loud because the selected-driver path does not yet
carry strength metadata through resolution. `constant_strength_select_driver`
supplies the differential witness.

The census remains **4,810 clean / 17,172 partial / 66 include skips**, with
`AssignmentExpression:target` unchanged at **3,036 files**. Differential
coverage moves **117/113/0/4 → 118/114/0/4**; grammar coverage remains
**214/83/131**.

## Literal `$assertcontrol` calls — 2026-10-24

A one-argument `$assertcontrol` call with an integral literal now lowers to an
inert statement. Assertion reporting controls are not represented in the
self-check state, so the call has no modeled value, output, or halt effect.
Dynamic, multi-argument, and assertion-observable forms remain loud.
`assertcontrol_literal` supplies the differential witness.

The census remains **4,810 clean / 17,172 partial / 66 include skips** with
unchanged blocker counts. Differential coverage moves **118/114/0/4 →
119/115/0/4**; grammar coverage remains **214/83/131**.

## Literal `$assertcontrol` argument lists — 2026-10-24

`$assertcontrol` with one or more integral literal arguments now lowers to an
inert statement. Assertion reporting controls are outside the self-check
state, so these calls have no modeled value, output, or halt effect. Dynamic
or hierarchical arguments remain loud. `assertcontrol_literal_args` supplies
the two-argument differential witness.

The census remains **4,810 clean / 17,172 partial / 66 include skips** with
unchanged blocker counts. Differential coverage moves **119/115/0/4 →
120/116/0/4**; grammar coverage remains **214/83/131**.

## Empty 2-state queue initializers — 2026-10-24

An empty queue initializer (`{}` or `'{}'`) on a 2-state queue now lowers to
inert declaration metadata. The flat self-check state has no queue object, and
an empty declaration contributes no observable value until a queue operation
uses it. Nonempty or effectful initializers, reads, writes, methods, and all
4-state queues remain loud. `empty_queue_decl` supplies the two initializer
forms and the differential witness.

The fresh 22,048-path census moves **4,810 → 4,816 clean** and
**17,172 → 17,166 partial**; `VariableSymbol:2state` falls **2,351 → 2,350**.
Differential coverage moves **120/116/0/4 → 121/117/0/4**; grammar coverage
remains **214/83/131**.

## Constant out-of-bounds writes to fixed-size dynamic arrays — 2026-10-24

After a single constant `new[N]` allocation of an integral 2-state dynamic
array, a constant out-of-range element write now lowers to `Empty`. IEEE
1800-2023 §7.4.5 specifies that the invalid write performs no update; the
existing flat-cell expansion already represents every in-range element. Dynamic
indices, resizes, aggregate values, unsupported leaves, and reads remain loud.
`dynamic_array_oob_write` supplies the differential witness.

The corpus census remains **4,816 clean / 17,166 partial / 66 include skips**;
the residual `AssignmentExpression:target` blocker remains **3,035 files**
because this exact shape is absent from the corpus snapshot. Differential
coverage moves **121/117/0/4 → 122/118/0/4**; grammar coverage remains
**214/83/131**.

## Literal `$rtoi` conversions — 2026-10-24

`$rtoi` with one finite real or short-real literal now lowers to the existing
signed 32-bit literal after IEEE 1800-2023 §20.5 truncation toward zero. The
same pure conversion is inert in statement position when its result is
discarded. Decimal spelling is converted without host floating-point rounding;
dynamic real reads and out-of-range results remain loud. `rtoi_literal` supplies
the value and discarded-result paths, while extractor tests pin the dynamic and
range boundaries.

The fresh 22,048-file census moves **4,817 → 4,823 clean** and **17,165 →
17,159 partial**; `CallExpression` falls **2,986 → 2,980**, with
`ExpressionStatement:CallExpression` unchanged at **2,985**. Differential
coverage moves **123/119/0/4 → 124/120/0/4**; grammar coverage remains
**214/83/131**.

## Literal `$realtobits` conversions — 2026-10-24

`$realtobits` with one direct finite real literal now lowers to the existing
64-bit literal containing that value's IEEE-754 encoding. A discarded call in
statement position is inert. Dynamic real storage, explicit conversion shells,
overflow, and other real-to-bits forms remain loud. `realtobits_literal`
supplies the value and discarded-result paths; extractor tests pin the exact
negative pattern and the dynamic, cast, and overflow boundaries.

The fresh 22,048-file census moves **4,823 → 4,828 clean** and **17,159 →
17,154 partial**; `CallExpression` falls **2,980 → 2,975**, with
`ExpressionStatement:CallExpression` unchanged at **2,985**. Differential
coverage moves **124/120/0/4 → 125/121/0/4**; grammar coverage remains
**214/83/131**.

## Literal `$shortrealtobits` conversions — 2026-10-24

`$shortrealtobits` with a direct finite real literal through its implicit
single-precision conversion shell now lowers to the existing 32-bit literal
containing the IEEE-754 single pattern. A discarded statement call is inert.
Dynamic values, explicit conversion shells, overflow, and other short-real
forms remain loud. `shortrealtobits_literal` supplies the value and discarded
result paths; extractor tests pin the exact negative pattern and the dynamic,
explicit-cast, and overflow boundaries.

The fresh 22,048-file census moves **4,828 → 4,829 clean** and **17,154 →
17,153 partial**; `CallExpression` falls **2,975 → 2,973**, with
`ExpressionStatement:CallExpression` unchanged at **2,985**. Differential
coverage moves **125/121/0/4 → 126/122/0/4**; grammar coverage remains
**214/83/131**.

## Floating type `$bits` queries — 2026-10-24

`$bits(real)` and `$bits(shortreal)` now lower to signed 32-bit literals from
fixed type metadata, yielding 64 and 32 respectively. The operand is a
`DataTypeExpression`, so no runtime real value is evaluated; named real and
shortreal variables, dynamic types, and other value queries remain loud.
`floating_bits_query` supplies the differential witness and the existing bit
query tests pin the runtime-value refusal.

The fresh 22,048-file census remains **4,829 clean / 17,153 partial / 66
include skips**, with `CallExpression` unchanged at **2,973** and
`ExpressionStatement:CallExpression` at **2,985** because the corpus has no
file containing only this metadata gap. Differential coverage moves
**126/122/0/4 → 127/123/0/4**; grammar coverage remains **214/83/131**.

## Literal `$rtoi($itor(...))` conversion — 2026-10-24

`$rtoi($itor(I))` now lowers to the signed 32-bit literal for one direct finite
integral literal `I`. IEEE 1800-2023 defines `$itor` as an exact integer to
real conversion, so the nested conversion can be folded without introducing
real storage. Named and computed integer operands remain loud; the existing
dynamic and range `$rtoi` boundaries are unchanged. `rtoi_itor_literal` is the
differential witness, and extractor tests pin the exact negative value and the
dynamic-input refusal.

The fresh 22,048-file census remains **4,829 clean / 17,153 partial / 66
include skips**, with `CallExpression` unchanged at **2,973** and
`ExpressionStatement:CallExpression` at **2,985** because the corpus has no
literal nested conversion. Differential coverage moves **127/123/0/4 →
128/124/0/4**; grammar coverage remains **214/83/131**.

## Literal `$realtobits($itor(...))` conversion — 2026-10-24

`$realtobits($itor(I))` now lowers to the exact 64-bit IEEE-754 encoding when
`I` is one direct finite integral literal. `$itor` is exact for this operand,
so the real conversion remains metadata-only; named or computed integer inputs
and explicit real casts stay loud. `realtobits_itor_literal` supplies the
differential witness, with extractor tests covering the exact negative pattern
and the dynamic-input refusal.

The fresh 22,048-file census remains **4,829 clean / 17,153 partial / 66
include skips**, with `CallExpression` unchanged at **2,973** and
`ExpressionStatement:CallExpression` at **2,985** because the corpus has no
literal nested conversion. Differential coverage moves **128/124/0/4 →
129/125/0/4**; grammar coverage remains **214/83/131**.

## Literal `$shortrealtobits($itor(...))` conversion — 2026-10-24

`$shortrealtobits($itor(I))` now lowers to the exact 32-bit IEEE-754 single
encoding when `I` is one direct finite integral literal. The existing implicit
short-real conversion shell is retained; named or computed integer inputs and
explicit casts remain loud. `shortrealtobits_itor_literal` supplies the
differential witness, with extractor tests pinning the negative pattern and
the dynamic-input refusal.

The fresh 22,048-file census remains **4,829 clean / 17,153 partial / 66
include skips**, with `CallExpression` unchanged at **2,973** and
`ExpressionStatement:CallExpression` at **2,985** because the corpus has no
literal nested conversion. Differential coverage moves **129/125/0/4 →
130/126/0/4**; grammar coverage remains **214/83/131**.

## Discarded literal `$itor` calls — 2026-10-24

A discarded `$itor` call with one direct finite integral literal is now erased.
The integer-to-real conversion is exact and has no modeled storage when its
result is unused; named or computed operands remain loud. The
`itor_literal_statement` witness supplies the differential evidence, with
extractor tests pinning the inert literal form and the dynamic-input refusal.

The fresh 22,048-file census remains **4,829 clean / 17,153 partial / 66
include skips**, with `CallExpression` unchanged at **2,973** and
`ExpressionStatement:CallExpression` at **2,985** because the corpus has no
literal discarded conversion. Differential coverage moves **130/126/0/4 →
131/127/0/4**; grammar coverage remains **214/83/131**.

## Discarded literal `$bitstoreal` calls — 2026-10-24

A discarded `$bitstoreal` call with one known 64-bit integral literal is now
erased because the conversion produces only an unrepresented real value.
Unknown and dynamic bit patterns remain loud. `bitstoreal_literal_statement`
supplies the differential witness, with extractor tests pinning the inert
literal form and dynamic-input refusal.

The fresh 22,048-file census remains **4,829 clean / 17,153 partial / 66
include skips**, with `CallExpression` unchanged at **2,973** and
`ExpressionStatement:CallExpression` at **2,985** because the corpus has no
literal discarded conversion. Differential coverage moves **131/127/0/4 →
132/128/0/4**; grammar coverage remains **214/83/131**.

## Discarded literal `$bitstoshortreal` calls — 2026-10-24

A discarded `$bitstoshortreal` call with one known 32-bit integral literal is
now erased because it produces only unrepresented single-precision real
storage. Unknown and dynamic bit patterns remain loud.
`bitstoshortreal_literal_statement` supplies the differential witness, with
extractor tests pinning the inert literal form and dynamic-input refusal.

The fresh 22,048-file census remains **4,829 clean / 17,153 partial / 66
include skips**, with `CallExpression` unchanged at **2,973** and
`ExpressionStatement:CallExpression` at **2,985** because the corpus has no
literal discarded conversion. Differential coverage moves **132/128/0/4 →
133/129/0/4**; grammar coverage remains **214/83/131**.

## Dynamic-array continuous-assignment targets — 2026-10-24

IEEE 1800-2023 §6.21 rejects a continuous assignment whose destination is an
element of a dynamic array: such elements may only be written procedurally.
The extractor now recognizes this elaboration-invalid target and emits an inert
process, so the self-check body can still run without fabricating dynamic-array
storage or a continuous-driver scheduler rule. Procedural dynamic-array writes,
reads, resizes, and all other dynamic targets remain loud. The
`dynamic_array_continuous_target` fixture supplies the PASS transcript and the
extractor test pins the rejected target metadata.

The fresh corpus census moves **4,829 → 4,830 clean** and **17,153 → 17,152
partial** (66 include skips); `AssignmentExpression:target` falls **3,035 →
3,034 files** because this compile-error target is now erased in the snapshot.
Differential coverage moves **133/129/0/4 → 134/130/0/4**;
grammar coverage remains **214/83/131**.

## Multiple continuous assignments to variables — 2026-10-24

IEEE 1800-2023 §10.3.2 permits at most one continuous assignment driver for a
variable. The extractor now recognizes a group of whole-variable continuous
assignments as an elaboration error and emits inert processes for the invalid
group. This preserves the compile-time rule without inventing variable-driver
resolution or a scheduler path. Nets keep their existing literal-resolution
rules; selected, dynamic, procedural, and single-driver variable forms retain
their existing boundaries. `multiple_variable_continuous_drivers` supplies the
PASS fixture and differential row, and extractor tests pin the rejected group.

The fresh census moves **4,830 → 4,833 clean** and **17,152 → 17,149 partial**
(66 include skips); `AssignmentExpression:target` falls **3,034 → 3,031**.
Differential coverage moves **134/130/0/4 → 135/131/0/4**; grammar coverage
remains **214/83/131**.

## Invalid floating associative-array indices — 2026-10-24

IEEE 1800-2023 §§7.8.4-7.8.5 reject floating-point associative-array keys and
implicit real-to-integral conversions when selecting an integral-keyed array.
The extractor now recognizes both invalid blocking target forms and emits inert
metadata, preserving the elaboration error without inventing associative-array
storage or key equality. Valid integral-key selections and all dynamic or
user-defined associative-array operations remain loud.
`invalid_associative_index_target` supplies both rejected forms and the PASS
transcript; extractor tests pin the floating-key and converted-selector cases.

The fresh corpus run measures **4,833 → 4,837 clean** and **17,149 → 17,146
partial** across **22,048 → 22,049 paths** (66 include skips).
`AssignmentExpression:target` falls **3,031 → 3,029**. Differential coverage
moves **135/131/0/4 → 136/132/0/4**; grammar coverage remains **214/83/131**.

## Invalid structure assignment-pattern replication — 2026-10-24

IEEE 1800-2023 §5.10 forbids replication inside a structure assignment pattern.
The extractor now recognizes this elaboration-invalid blocking write and emits
inert metadata, so no aggregate structure store is fabricated. Valid structure
patterns, aggregate copies, and other replication forms remain on their existing
boundaries. `invalid_struct_replication_assignment` supplies the PASS fixture
and extractor tests pin the rejected replicated pattern.

The fresh 22,049-path census moves **4,837 → 4,838 clean** and **17,146 →
17,145 partial** (66 include skips); `AssignmentExpression:target` falls
**3,029 → 3,028**. Differential coverage moves **136/132/0/4 → 137/133/0/4**;
grammar coverage remains **214/83/131**.

## Invalid unknown string-replication multipliers — 2026-10-24

IEEE 1800-2023 §6.16 requires a string-replication multiplier to be a known
nonnegative integral value. A multiplier initialized to all `x`/`z` bits is an
elaboration-invalid form; the extractor now recognizes that exact constant
shape and emits inert metadata without adding string storage. Valid literal and
dynamic string replication remains loud. `invalid_string_replication_multiplier`
supplies the PASS fixture and the extractor test pins the unknown-multiplier
boundary.

The fresh 22,049-path census moves **4,838 → 4,839 clean** and **17,145 →
17,144 partial** (66 include skips); `AssignmentExpression:target` falls
**3,028 → 3,027**. Differential coverage moves **137/133/0/4 → 138/134/0/4**;
grammar coverage remains **214/83/131**.

## Literal semaphore constructors — 2026-10-24

The opaque class-handle boundary now admits `semaphore = new(N)` when `N` is
a known nonnegative integral literal. The constructor's key store has no
representation in the self-check state, and later semaphore operations remain
loud, so the write can be erased without fabricating synchronization state.
Dynamic, negative, computed, and method-using forms remain loud.
`literal_semaphore_constructor` supplies the PASS fixture; extractor tests pin
the literal and dynamic constructor boundaries.

The fresh 22,049-path census moves **4,839 → 4,840 clean** and **17,144 →
17,143 partial** (66 include skips). `AssignmentExpression:target` falls
**3,028 → 2,980**, moving `ExpressionStatement:CallExpression` to the leading
blocker at **2,985**. Differential coverage moves **138/134/0/4 → 139/135/0/4**;
grammar coverage remains **214/83/131**.

## Dynamic-to-fixed size-mismatch assignments — 2026-10-24

IEEE 1800-2023 §7.6 requires a run-time error, with no copy, when a sampled
dynamic array is assigned to a fixed-size unpacked array of a different
length. The flat self-check state has no diagnostic stream or aggregate store,
so this exact blocking form lowers to an immediate `$finish`, preserving the
observable halt and preventing later statements from running. Equal-size
copies, nonblocking/timed assignments, effectful sources, and all other
dynamic-array operations remain loud. `dynamic_fixed_size_mismatch` supplies
the `BEFORE` transcript and the extractor tests pin the mismatch and equal-size
boundaries.

## Single dynamic selectors in finite multidimensional arrays — 2026-10-26

Assignments and reads with exactly one dynamic selector in any unpacked
dimension of a finite multidimensional integral array now dispatch through the
flat cell expansion. All other dimensions must be constant; multiple dynamic
selectors and aggregate leaves remain loud. The nested dynamic-target fixtures
cover both inner and outer selectors, with extractor regressions for the
admitted and rejected shapes.

## Innermost dynamic selectors in finite multidimensional arrays — 2026-10-26

Assignments and reads with one dynamic selector in the innermost dimension of
a finite multidimensional integral array now dispatch through the existing
cell expansion. All enclosing dimensions must be constant; outer dynamic
selectors, multiple dynamic selectors, and aggregate leaves remain loud. The
`nested_fixed_array_dynamic_target` fixture supplies the differential row and
Lean receipt, with extractor regressions for the admitted and rejected shapes.

## Pure literal integral continuous expressions — 2026-10-26

Continuous assignment now folds an all-literal unsigned integral arithmetic or
bitwise expression into the existing time-zero driver. The fold is restricted
to known 0/1 leaves and side-effect-free operators; variables, X/Z operands,
signed or dynamic expressions, and effectful calls remain live or loud. The
`constant_expression_net_driver` fixture supplies the differential row and
Lean receipt, with extractor regressions for the fold and variable boundary.

## Unsized left streaming over one-bit leaves — 2026-10-26

Left-streaming assignment now accepts the IEEE default one-bit chunk when
every direct target leaf is one bit. The existing sampled-vector lowering is
reused; wider unsized leaves, explicit dynamic forms, nested streams, and
aggregate targets remain loud. The `unsized_left_stream` fixture supplies the
differential row and Lean receipt, with extractor regressions for the default
and wider-leaf boundaries.

The 22,049-path census moves **4,841 → 4,842 clean** and **17,142 → 17,141
partial** (66 include skips); `AssignmentExpression:target` falls **2,980 →
2,979**. Differential coverage moves **141/137/0/4 → 142/138/0/4**; grammar
coverage remains **214/83/131**.


## Literal `$sformat` writes to packed integrals — 2026-10-24

IEEE 1800-2023 §§5.9 and 21.3.3 assign a plain literal `$sformat` result to
the output integral in packed-byte order: right aligned, left padded, or
truncated. The self-check surface now lowers exactly that two-argument form to
an ordinary blocking assignment. Conversion markers, dynamic arguments,
selected or effectful targets, and string-output or other formatting calls
remain loud. `sformat_literal_integral` supplies the `PASS` transcript and
extractor tests pin the literal, dynamic-format, and selected-target
boundaries.

The 22,049-path census moves **4,842 → 4,843 clean** and **17,141 → 17,140
partial** (66 include skips); `ExpressionStatement:CallExpression` falls
**2,984 → 2,983**. Differential coverage moves **142/138/0/4 → 143/139/0/4**;
grammar coverage remains **214/83/131**.

## Source-pure real and time arguments in severity tasks — 2026-10-24

IEEE 1800-2023 §20.10 permits `$info`, `$warning`, and `$error` to use the
same display-style argument list as `$display`. The self-check state has no
severity diagnostic stream and no floating storage, so these tasks now erase a
literal format call when every argument is source-pure: integral reads,
literal strings, real/shortreal reads or literals, and zero-time `$time` /
`$realtime` queries. Calls through functions, mutable or unsupported values,
and nonliteral formats remain loud. `severity_opaque_args` supplies the
real/time differential witness; extractor tests pin the string-variable and
effectful-real boundaries.

The fresh 22,048-path census moves **4,841 → 4,842 clean** and **17,141 →
17,140 partial** (66 include skips); `ExpressionStatement:CallExpression`
falls **2,983 → 2,982**. Differential coverage moves **143/139/0/4 →
144/140/0/4**; grammar coverage remains **214/83/131**.

## Constant formatted writes to packed selections — 2026-10-24

IEEE 1800-2023 §21.3.3 permits `$sformat` and `$swrite` to write formatted
text through an output variable. The self-check slice now admits the narrow
constant form for an integral packed variable or fixed packed selection:
literal format, literal integral or string arguments, and right-aligned
byte-to-bit conversion through the existing blocking-assignment machinery.
Dynamic arguments, unsupported format directives, string storage, aggregate
targets, and effectful or timed writes remain loud. The
`sformat_constant_selected` fixture and extractor tests cover `%b`, `%s:%0d`,
and `$swrite` on a selected target.

The fresh 22,048-path census remains **4,843 clean / 17,139 partial** (66
include skips); `ExpressionStatement:CallExpression` falls **2,982 → 2,981**.
Differential coverage moves **144/140/0/4 → 145/141/0/4**; grammar coverage
remains **214/83/131**.

## Literal fixed-array `reverse()` — 2026-10-24

IEEE 1800-2023 §7.12.2 reverses the elements of an unpacked array in place.
The self-check surface already stores fixed unpacked integral leaves as
independent cells, so the extractor now lowers `reverse()` on a one-dimensional
fixed array with a complete scalar literal initializer to cell writes in
reverse order. Dynamic arrays, queues, multidimensional arrays, nonliteral
initializers, and other receiver uses remain loud. `array_reverse` supplies
the `PASS` transcript; extractor tests pin the dynamic and nonliteral refusal
boundaries.

The fresh **22,049-path** census measures **4,846 clean / 17,137 partial** (66
include skips); the committed 22,048-path snapshot is superseded by the
corpus update, while `ExpressionStatement:CallExpression` falls **2,981 →
2,980**. Differential coverage moves **145/141/0/4 → 146/142/0/4**; grammar
coverage remains **214/83/131**.

## Queue initialization status results — 2026-10-24

IEEE 1800-2023 §20.15.6 defines scalar status results for queue initialization.
When a file contains no other queue task, the self-check surface now lowers a
four-argument `$q_initialize` with literal type and capacity to a blocking
status write: valid FIFO/LIFO creation reports 0, an unsupported type reports
4, and a nonpositive capacity reports 5. Queue storage, duplicate IDs, and
all subsequent queue operations remain loud. `q_initialize_status` supplies
the status-4 differential witness; extractor tests cover statuses 0 and 5 and
the stateful refusal boundary.

The fresh **22,049-path** census moves **4,846 → 4,852 clean** and **17,137 →
17,131 partial** (66 include skips). `ExpressionStatement:CallExpression`
falls **2,980 → 2,974**, while `AssignmentExpression:target` is the new
leading blocker at **2,979**. Differential coverage moves **146/142/0/4 →
147/143/0/4**; grammar coverage remains **214/83/131**.

## Explicit-slice right-streaming targets — 2026-10-24

The target tier now admits IEEE 1800-2023 §11.4.14.3 right-streaming unpack
with a positive explicit slice size or a fixed built-in integral slice type.
Numeric sizes and `byte`/`shortint`/`int`/`integer`/`longint`/`time` are resolved
at extraction, and direct equal-width scalar or flattened fixed-array leaves
reuse the existing sampled `ConcatTarget` write. Mixed widths, `with` clauses,
nested or dynamic targets, and other non-integral forms remain loud.

`streaming_slice_target` is the differential witness. The fresh 22,049-path
census remains **4,852 clean / 17,131 partial / 66 include skips** and lowers
`AssignmentExpression:target` **2,979 → 2,978**; differential coverage moves
**147/143/0/4 → 148/144/0/4**, with grammar coverage unchanged at
**214/83/131**.

## Named-type left-streaming targets — 2026-10-24

The target tier now resolves a positive built-in integral type such as `byte`
as the slice of a left-streaming unpack. Equal-width scalar or flattened
fixed-cell leaves reuse the existing low-chunk-first `ConcatTarget` write, so
the source chunks are reversed exactly once. Unsized streams, mixed widths,
`with` clauses, and dynamic or nested targets remain loud.

`streaming_left_slice_target` is the differential witness. The fresh
22,049-path census remains **4,852 clean / 17,131 partial / 66 include skips**
with `AssignmentExpression:target` at **2,978**; differential coverage moves
**148/144/0/4 → 149/145/0/4**, with grammar coverage unchanged at
**214/83/131**.

## Shallow unpacked-union member targets — 2026-10-24

The legacy self-check surface now represents an untagged unpacked union with
one flat vector cell when every direct member is an equal-width integral value
of the same state kind. Member reads and blocking writes through any member
therefore preserve the union aliasing rule without an aggregate store. Tagged,
unequal-width, mixed-state, nested, whole-union, nonblocking, and timed forms
remain loud. `unpacked_union_member` supplies the differential witness.

The fresh **22,049-path** census moves **4,852 → 4,853 clean** and **17,131 →
17,130 partial** (66 include skips); `AssignmentExpression:target` falls
**2,978 → 2,977**. Differential coverage moves **149/145/0/4 → 150/146/0/4**;
grammar coverage remains **214/83/131**.

## Shallow unpacked-union whole copies — 2026-10-24

Blocking whole-value assignments between equal-width integral members of the
admitted shallow untagged unpacked-union shape now copy the one shared flat
vector cell. Reads through either destination member therefore preserve the
union aliasing rule. Tagged, mixed-width, initialized, member-to-whole,
nonblocking, and timed forms remain loud. `unpacked_union_copy` supplies the
differential witness.

The fresh **22,049-path** census moves **4,853 → 4,855 clean** and
**17,130 → 17,128 partial** (66 include skips); `AssignmentExpression:target`
falls **2,977 → 2,975**. Differential coverage moves **150/146/0/4 →
151/147/0/4**; grammar coverage remains **214/83/131**.

## Shallow unpacked-union whole-value comparisons — 2026-10-24

Whole values of the admitted shallow untagged unpacked-union shape now read
from their shared flat cell for `==`, `!=`, `===`, and `!==`. This preserves
logical and case equality through alternate member writes while keeping union
arithmetic and other aggregate operations loud. `unpacked_union_equality`
supplies the differential witness.

The fresh **22,049-path** census remains **4,855 clean / 17,128 partial**
(66 include skips), with `AssignmentExpression:target` at **2,975**.
Differential coverage moves **151/147/0/4 → 152/148/0/4**; grammar coverage
remains **214/83/131**.

## Shallow unpacked-union conditional values — 2026-10-25

A conditional expression between two equal-width integral values of the
admitted shallow untagged unpacked-union shape now selects their shared flat
cells through the ordinary `Ternary` path. Mixed shapes, aggregate arms,
union arithmetic, and scheduled forms remain loud. `unpacked_union_conditional`
supplies the differential witness.

The fresh **22,049-path** census remains **4,855 clean / 17,128 partial**
(66 include skips), with `AssignmentExpression:target` at **2,975**.
Differential coverage moves **152/148/0/4 → 153/149/0/4**; grammar coverage
remains **214/83/131**.

## Shallow unpacked-union compound member updates — 2026-10-25

A blocking compound assignment through a direct member of the admitted shallow
untagged unpacked-union shape now performs its read-modify-write on the shared
flat cell. Nonblocking, timed, mixed-shape, and unsupported compound operators
remain loud. `unpacked_union_compound` supplies the differential witness.

The fresh **22,049-path** census remains **4,855 clean / 17,128 partial**
(66 include skips), with `AssignmentExpression:target` at **2,975**.
Differential coverage moves **153/149/0/4 → 154/150/0/4**; grammar coverage
remains **214/83/131**.

## Shallow unpacked-union case subjects — 2026-10-25

An ordinary `case` subject may now read a direct equal-width integral member of
the admitted shallow untagged unpacked-union shape. The subject reuses the
shared flat cell and the existing case lowering, so a write through one member
selects a matching item named through another. Tagged, unequal-width, nested,
effectful, and scheduled subjects remain loud. `unpacked_union_case_member`
supplies the differential witness.

The fresh **22,049-path** census remains **4,855 clean / 17,128 partial** (66
include skips), with `AssignmentExpression:target` at **2,975**. Differential
coverage moves **154/150/0/4 → 155/151/0/4**; grammar coverage remains
**214/83/131**.

## Zero-key semaphore `try_get` — 2026-10-25

IEEE 1800-2023 §15.3.4 defines `semaphore.try_get(0)` as an immediate
successful attempt returning a positive value; it consumes no keys. The
self-check surface represents that positive result as scalar `1` when the
receiver has a preceding literal `new(...)` constructor and the count is
exactly zero. Dynamic counts, unproven receivers, and nonzero or otherwise
stateful semaphore operations remain loud. `semaphore_zero_try_get` supplies
the differential witness.

The fresh **22,049-path** census moves **4,855 → 4,856 clean** and **17,128 →
17,127 partial** (66 include skips); `CallExpression` falls **2,973 → 2,972**
while `AssignmentExpression:target` remains **2,975**. Differential coverage
moves **155/151/0/4 → 156/152/0/4**; grammar coverage remains **214/83/131**.

## Empty mailbox `num()` queries — 2026-10-25

An untouched mailbox created by literal `new()` now answers `num()` with the
exact scalar value zero. The receiver must have a constructor witness and no
later mailbox operation; method calls that could observe queued messages remain
loud. The generic empty-function shortcut no longer fabricates a result for
mailbox `num()` calls, closing that wrong-answer path. `mailbox_empty_num`
supplies the differential witness.

The fresh **22,049-path** census remains **4,856 clean / 17,127 partial** (66
include skips). `CallExpression` is **3,026**, up from **2,972**, because
previously fabricated mailbox-method values are now explicit refusals;
`AssignmentExpression:target` remains **2,975**. Differential coverage moves
**156/152/0/4 → 157/153/0/4**; grammar coverage remains **214/83/131**.

## Literal unbounded mailbox puts and counts — 2026-10-25

An unbounded mailbox created by literal `new()` now admits source-pure literal
`put` calls and an exact `num()` count for the same direct handle. The lowering
counts only preceding puts and keeps aliases, bounded constructors, other
methods, dynamic arguments, and calls before construction loud; this preserves
the mailbox's observable count without inventing a mailbox object in the flat
self-check store. `mailbox_literal_put_num` supplies the differential witness.

The fresh **22,049-path** census remains **4,856 clean / 17,127 partial** (66
include skips), with `CallExpression` at **3,026** and
`AssignmentExpression:target` at **2,975**. Differential coverage moves
**157/153/0/4 → 158/154/0/4**; grammar coverage remains **214/83/131**.

## Literal string length after assignments — 2026-10-25

String `.len()` queries now follow a source-pure literal assignment history.
Each query uses the most recent literal string value for that handle, while
dynamic writes, aliases, non-ASCII values, and other string operations remain
loud. `string_len_assignment` supplies the differential witness.

The fresh **22,049-path** census moves **4,856 → 4,865 clean** and **17,127 →
17,118 partial** (66 include skips); `CallExpression` falls **3,026 → 3,017**
while `AssignmentExpression:target` remains **2,975**. Differential coverage
moves **158/154/0/4 → 159/155/0/4**; grammar coverage remains **214/83/131**.

## Literal string `atoi()` conversions — 2026-10-25

String `.atoi()` calls now scan the latest source-pure ASCII literal value for
leading decimal digits and underscores, stopping at the first other character
and returning the exact signed 32-bit result. Dynamic writes, signs, base
prefixes, overflow, non-ASCII values, and other string methods remain loud.
`string_atoi_literal` supplies the differential witness.

The corpus snapshot now has **22,050 paths** after an upstream fixture update;
relative to the previous **22,049-path** measurement, this item moves clean
files **4,856 → 4,875** and partial files **17,127 → 17,109** (66 include
skips), with `CallExpression` falling **3,017 → 3,007**. Differential coverage
moves **159/155/0/4 → 160/156/0/4**; grammar coverage remains **214/83/131**.

## Literal string `compare()` and `icompare()` — 2026-10-25

Source-pure ASCII string comparisons now return the normalized `-1`, `0`, or
`1` ordering result. `icompare()` folds ASCII case before comparing. Dynamic
writes, non-ASCII values, unsupported string methods, and other effects remain
loud. `string_compare_literal` supplies the differential witness.

The 22,050-path census moves **4,875 → 4,888 clean** and **17,109 → 17,096
partial** (66 include skips); `CallExpression` falls **3,007 → 2,994** while
`AssignmentExpression:target` remains **2,975**. Differential coverage moves
**160/156/0/4 → 161/157/0/4**; grammar coverage remains **214/83/131**.
## Literal semaphore `try_get` state sequences — 2026-10-25

The self-check surface now evaluates source-ordered `try_get` calls on a
direct semaphore constructed with a nonnegative literal key count. Each call
uses a literal count (including the standard default of one), returns scalar
`1` on success and `0` when insufficient keys remain, and subtracts keys only
on success. Aliases, reassignment, negative or dynamic counts, and other
semaphore methods remain loud because the flat state does not represent a
semaphore object. `semaphore_literal_try_get` is the executable fixture and
proof receipt.

The 22,050-path census moves 4,888 → 4,901 clean and 17,096 → 17,083
partial (66 include skips). `CallExpression` falls 2,994 → 2,982 and
`ExpressionStatement:CallExpression` falls 2,974 → 2,973; the next blocker
`AssignmentExpression:target` remains 2,975. Differential coverage moves
161/157/0/4 → 162/158/0/4; grammar coverage remains 214/83/131.

## Literal dynamic-array `size()` after allocation — 2026-10-25

The self-check surface now answers `size()` exactly for a dynamic array with
one sampled positive literal `new[N]` allocation. The flat store already
expands that allocation into independent cells, so the length is the same
literal scalar fact. Resizing, deletion, dynamic bounds, aliases, and other
array methods remain loud. `dynamic_array_literal_size` supplies the fixture,
differential row, and proof receipt.

The 22,050-path census moves 4,901 → 4,906 clean and 17,083 → 17,078
partial (66 include skips). `CallExpression` falls 2,982 → 2,965 and the
leading `AssignmentExpression:target` blocker remains 2,975; the next
`ExpressionStatement:CallExpression` blocker remains 2,973. Differential
coverage moves 162/158/0/4 → 163/159/0/4; grammar coverage remains 214/83/131.
## Literal string radix conversions — 2026-10-25

The self-check surface now admits source-pure literal string `atobin()`,
`atooct()`, and `atohex()` calls with 32-bit integral results. Valid radix
digits are converted exactly; `x`, `z`, and `?` preserve their four-state
unknown bits at the corresponding radix width. Dynamic strings, invalid
digits, unsupported methods, and non-32-bit results remain loud.
`string_radix_literal` supplies the executable fixture and proof receipt.

The 22,050-path census moves 4,906 → 4,910 clean and 17,078 → 17,074
partial (66 include skips). `CallExpression` falls 2,965 → 2,958 while
`AssignmentExpression:target` remains 2,975 and
`ExpressionStatement:CallExpression` remains 2,973. Differential coverage
moves 163/159/0/4 → 164/160/0/4; grammar coverage remains 214/83/131.
## Default-zero literal semaphore `try_get` — 2026-10-25

The literal semaphore sequence now also accepts the standard `new()` form,
whose default key count is zero. A subsequent literal `try_get(k)` therefore
returns scalar zero without consuming keys. The existing direct-constructor,
source-order, alias, dynamic-count, and mixed-method guards remain in force;
all other semaphore behavior stays loud. `semaphore_default_try_get` supplies
the fixture and proof receipt.

The 22,050-path census moves 4,910 → 4,912 clean and 17,074 → 17,072
partial (66 include skips). `CallExpression` falls 2,958 → 2,956 while
`AssignmentExpression:target` remains 2,975 and
`ExpressionStatement:CallExpression` remains 2,973. Differential coverage
moves 164/160/0/4 → 165/161/0/4; grammar coverage remains 214/83/131.
## Empty mailbox `try_get` and `try_peek` — 2026-10-25

An untouched unbounded mailbox created by direct `new()` now answers both
`try_get(output)` and `try_peek(output)` with exact scalar zero. The output
argument is retained as an ordinary destination, while aliases, queued or
bounded mailboxes, other methods, and mixed operations remain loud because no
mailbox object is represented in the flat state. `mailbox_empty_try` supplies
the fixture and proof receipt.

The 22,050-path census moves 4,912 → 4,917 clean and 17,072 → 17,067
partial (66 include skips). `CallExpression` falls 2,956 → 2,951 while
`AssignmentExpression:target` remains 2,975 and
`ExpressionStatement:CallExpression` remains 2,973. Differential coverage
moves 165/161/0/4 → 166/162/0/4; grammar coverage remains 214/83/131.
## Untriggered and null event status — 2026-10-25

An event's `triggered()` query now lowers to exact one-bit zero when the
source contains no trigger and the event is either uninitialized or explicitly
reclaimed with `null`. Event triggers, waits, other event methods, aliases, and
dynamic event state remain loud because scheduling state is outside this flat
self-check representation. `event_triggered_false` supplies the fixture and
proof receipt.

The 22,050-path census moves 4,917 → 4,921 clean and 17,067 → 17,063
partial (66 include skips). `CallExpression` falls 2,951 → 2,947 while
`AssignmentExpression:target` remains 2,975 and
`ExpressionStatement:CallExpression` remains 2,973. Differential coverage
moves 166/162/0/4 → 167/163/0/4; grammar coverage remains 214/83/131.

## Dynamic-array unpacked concatenation — 2026-10-25

An assignment of a finite unpacked concatenation of scalar integral values to a
dynamic array now samples the concatenation's exact length and lowers each
element to the existing flat dynamic-array cells. The declaration/allocation
path, constant indexed reads and writes, and `size()` therefore observe the
same values as the source operation without adding an aggregate store. Empty,
dynamic, effectful, aliased, and nonintegral aggregate forms remain loud; a
function-call element is pinned by `dynamic_array_concat_refuse` as a recorded
refusal.

The 22,050-path census moves **4,921 → 4,922 clean** and **17,063 → 17,062
partial** (66 include skips). `AssignmentExpression:target` falls **2,975 →
2,974** and `CallExpression` falls **2,947 → 2,939**; the other leading
blockers are unchanged. Differential coverage moves **167/163/0/4 →
169/164/0/5**; grammar coverage remains **214/83/131**.

## Dynamic-array concatenations with fixed-array operands — 2026-10-25

A finite unpacked concatenation assigned to a scalar-integral dynamic array
may now include fixed unpacked scalar arrays. Each operand is sampled in source
order and expanded into the destination's existing flat cells, preserving the
exact concatenation length, two-state conversion, and destination alias guard.
Nested aggregate, effectful, aliased, nonintegral, nonblocking, and timed
forms remain loud. The `dynamic_array_concat_subarrays` fixture covers the
`{1, middle, 4, tail}` shape.

The 22,053-path census moves **4,990 → 4,992 clean** and **16,996 → 16,994
partial** (67 include skips). `AssignmentExpression:target` falls **2,940 →
2,937** and `ElementSelectExpression:source-type` falls **549 → 546**.
Differential coverage moves **188/183/0/5 → 189/184/0/5**; grammar coverage
remains **214/86/128**.

## Dynamic-array positional assignment patterns — 2026-10-25

An exact positional assignment pattern of scalar integral values now samples a
dynamic array's finite extent and lowers each element to its existing flat
cells. This reuses the same source-order and two-state conversion path as the
unpacked concatenation rung. Nested, keyed/default, aliased, effectful,
nonintegral, and nonblocking or timed patterns remain loud. The real §10.9
shape is covered by `dynamic_array_pattern` and its Lean receipt.

The 22,050-path census moves **4,922 → 4,923 clean** and **17,062 → 17,061
partial** (66 include skips). `AssignmentExpression:target` falls **2,974 →
2,971**; `ExpressionStatement:CallExpression` and `CallExpression` remain
2,973 and 2,939. Differential coverage moves **169/164/0/5 → 170/165/0/5**;
grammar coverage remains **214/83/131**.

## Null-command `$system` task — 2026-10-25

The exact no-argument task form `$system()` is now admitted as an inert
self-check statement. IEEE §20.17.1 calls `system(NULL)` and discards the
status in task position; the flat state has no host-process or diagnostic
channel. String-command forms remain loud because they carry external effects.
The `system_null` fixture and differential row cover the admitted form.

The 22,050-path census moves **4,923 → 4,924 clean** and **17,061 → 17,060
partial** (66 include skips). `ExpressionStatement:CallExpression` falls
**2,973 → 2,972**; `AssignmentExpression:target` and `CallExpression` remain
2,971 and 2,939. Differential coverage moves **170/165/0/5 → 171/166/0/5**;
grammar coverage remains **214/83/131**.

## Variable standard-output MCD `$fdisplay` — 2026-10-25

`$fdisplay` now accepts a direct 32-bit integer descriptor variable when the
same initial block assigns it exactly once from the predefined stdout MCD
(`1` or `32'h8000_0001`) before the call. The lowering substitutes the
existing `$display` stream; computed, conditional, aliased, reassigned,
nonblocking, and nonstandard descriptor forms remain loud. The
`fdisplay_mcd_variable` fixture and extractor regressions cover the admitted
and refusal boundaries, with a Lean fixture receipt and differential row.

The 22,050-path census moves **4,924 → 4,925 clean** and **17,060 → 17,059
partial** (66 include skips). `ExpressionStatement:CallExpression` falls
**2,972 → 2,971**, tying `AssignmentExpression:target` at 2,971; `CallExpression`
remains 2,939. Differential coverage moves **171/166/0/5 → 172/167/0/5**;
grammar coverage remains **214/83/131**.

## Source-pure `string.atoreal()` writes to real storage — 2026-10-25

When a blocking assignment writes `string.atoreal()` from a proven ASCII
literal history into a named `real` or `shortreal`, the self-check tier now
erases the write. Real storage is opaque and the conversion has no represented
effect in this slice; dynamic or aliased string histories, non-ASCII values,
observed real reads, nonblocking writes, and timed assignments remain loud.
The `string_atoreal_real_write` fixture, extractor regressions, Lean receipt,
and differential row cover the admitted shape and its boundaries.

The fresh 22,050-path census remains **4,925 clean / 17,059 partial** (66
include skips); `AssignmentExpression:target` falls **2,971 → 2,967**. The
differential coverage moves **172/167/0/5 → 173/168/0/5** and grammar coverage
remains **214/83/131**.

## Literal semaphore `put`/`get` balance — 2026-10-25

Direct literal semaphore constructors now carry a source-ordered key balance
through literal `put(n)` and immediately completing `get(n)` calls. A `get`
is erased only when the statically tracked bucket contains enough keys; later
literal `try_get` expressions observe the consumed balance. Aliases, dynamic
counts, other methods, and calls that would block remain loud because the flat
self-check state does not represent semaphore objects or scheduler waiters.
The `semaphore_literal_put_get` fixture and its Lean receipt provide the
differential witness.

On the available 21,342-path sv-tests-2 snapshot, clean files move **4,840 →
4,861** and partial files **16,473 → 16,452** (29 include skips). The leading
`CallExpression` blocker falls **2,802 → 2,782** and
`ExpressionStatement:CallExpression` falls **2,668 → 2,644**. Differential
coverage grows **173/168/0/5 → 174/169/0/5**; grammar coverage remains
**214/83/131**.

## Dynamic-extent streaming `with` targets — 2026-10-25

Right-streaming unpack now admits a finite dynamic-array target whose
`with [base +: count]` extent is an integral variable assigned exactly once
from a literal before the stream. The extractor samples that source-ordered
extent, expands the already allocated array into flat cells, and reuses the
existing leading-bit stream window. Control-dependent, multiply assigned,
out-of-range, descending, aggregate, and effectful forms remain loud because
the flat self-check state has no general dynamic target node. The
`streaming_dynamic_with_range` fixture and differential row exercise the
admitted §11.4.14.4 shape.

On the available 21,342-path snapshot, clean files move **4,861 → 4,862** and
partial files **16,452 → 16,451** (29 include skips); the leading
`AssignmentExpression:target` blocker falls **2,794 → 2,793**. Differential
coverage grows **174/169/0/5 → 175/170/0/5** with no disagreements, and grammar
coverage remains **214/83/131**.

## Dynamic-array struct default allocation — 2026-10-25

Finite dynamic arrays whose element type is an untagged unpacked struct now
lower to one flat cell per integral field. A single constant `new[N]` samples
the extent, and each element receives the IEEE default value for every field;
field initializers are preserved and two-state fields are squashed at the
declaration boundary. Four-state, tagged, nested-array, union, and other
aggregate fields remain loud. The `dynamic_array_struct_defaults` and
`dynamic_array_struct_field_defaults` fixtures provide the §7.5.1 witnesses,
with extractor regressions covering both defaults and the four-state refusal.

On the available 21,342-path snapshot, clean files move **4,862 → 4,864** and
partial files **16,451 → 16,449** (29 include skips). `VariableSymbol:2state`
falls **2,246 → 2,243**; the remaining leading blockers are unchanged.
Differential coverage grows **175/170/0/5 → 177/172/0/5** with no
disagreements, and grammar coverage remains **214/83/131**.

## Streaming `with` extent from an earlier target — 2026-10-25

Right-streaming unpack now admits the §11.4.14.4 form where a dynamic-array
`with [base +: count]` extent refers to a target unpacked earlier in the same
stream, such as `{>> {len, payload with [0 +: len]}}`. The extractor samples a
single unconditional constant source assignment, uses the source prefix to
resolve the extent, and lowers the prefix plus selected array cells to the
existing flat target window. Computed or multiply assigned sources, aliases,
dynamic bases, and other stream shapes remain loud. The
`streaming_with_previous_extent` fixture and extractor acceptance/refusal
regressions cover this boundary.

On the available 21,342-path snapshot, clean files move **4,864 → 4,865** and
partial files **16,449 → 16,448** (29 include skips). The leading
`AssignmentExpression:target` blocker falls **2,793 → 2,792**. Differential
coverage grows **177/172/0/5 → 178/173/0/5** with no disagreements, and grammar
coverage remains **214/83/131**.

## Finite four-state dynamic-array cells — 2026-10-25

Finite dynamic arrays of four-state scalar or supported untagged integral
struct elements now use the existing flat-cell representation after one
constant `new[N]` allocation. Cells retain their four-state x defaults, while
constant and runtime-indexed reads and writes use the same bounded lowering as
the two-state dynamic-array path. Unallocated, resized, aliased, tagged,
union, nested-array, and other aggregate forms remain loud; no dynamic heap or
second scheduler is introduced. `dynamic_array_four_state` supplies the
differential fixture and Lean receipt, and the declaration tests cover both
scalar indexing and struct-field defaults.

On the paired 21,342-path snapshot, clean files move **4,865 → 4,867** and
partial files **16,448 → 16,446** (29 include skips). The leading
`AssignmentExpression:target` blocker remains **2,792**; the residual
`VariableSymbol:type` wall falls **60 → 57**. Differential coverage grows
**178/173/0/5 → 179/174/0/5** with no disagreements, and grammar coverage
remains **214/83/131**.

## Finite dynamic-array resize copies — 2026-10-25

A blocking `dst = new[N](src)` now lowers for two distinct, finite sampled
dynamic arrays whose scalar integral elements have the same width. The
destination receives one flat-cell copy per source position and the remaining
cells receive their IEEE default (zero for two-state elements, x for
four-state elements). Self-resize, declaration-time copies, dynamic sizes,
aliases, width mismatches, nested arrays, aggregate elements, and scheduled
forms remain loud; no heap resize or second scheduler is introduced.
`dynamic_array_resize_copy` supplies the differential fixture and Lean receipt,
with extractor regressions covering the admitted copy and the declaration-time
boundary.

The paired 21,342-path census remains **4,867 clean → 4,867 clean** and
**16,446 partial → 16,446 partial** (29 include skips); the leading
`AssignmentExpression:target` blocker remains **2,792**. Differential coverage
moves **179/174/0/5 → 180/175/0/5** with no disagreements, and grammar
coverage remains **214/83/131**.

## Finite dynamic-array copies from fixed sources — 2026-10-25

A blocking `dst = new[N](fixed_source)` now lowers for a distinct finite
one-dimensional fixed source and scalar integral destination with equal element
width. Source cells are copied in declared range order, and a larger destination
receives its two-state zero or four-state x default in the
remaining cells; a smaller destination truncates after its final cell.
Conversion-wrapped source expressions are accepted only when they resolve to
that same fixed storage. Dynamic sizes, self-aliasing, queues, nested or
aggregate elements, width mismatches, declaration-time copies, and scheduled
forms remain loud. `dynamic_array_resize_fixed_source` supplies the differential
fixture and Lean receipt, while extractor tests retain the aggregate and
initializer boundaries.

The paired 21,342-path census moves **4,867 clean → 4,875 clean** and
**16,446 partial → 16,438 partial** (29 include skips);
`AssignmentExpression:target` falls **2,792 → 2,784**. Differential coverage
moves **180/175/0/5 → 181/176/0/5** with no disagreements, and grammar coverage
remains **214/83/131**.

## Finite dynamic-array self-grow — 2026-10-25

A blocking `a = new[N](a)` now lowers for one sampled scalar dynamic array
whose preceding allocation has a smaller positive literal extent and whose new
extent is also a positive literal. The extractor captures every old flat cell
in an automatic temporary before writing the destination cells, preserving
source values and applying two-state zero padding or four-state x padding.
Self-shrink, repeated or dynamic resize, aliases, aggregate elements, and
scheduled forms remain loud; no heap object or second scheduler is introduced.
`dynamic_array_self_resize` supplies the differential fixture and Lean receipt,
and extractor tests pin capture ordering and shrink refusal.

The paired 21,342-path census moves **4,875 clean → 4,879 clean** and
**16,438 partial → 16,434 partial** (29 include skips);
`AssignmentExpression:target` falls **2,784 → 2,776**. Differential coverage
moves **181/176/0/5 → 182/177/0/5** with no disagreements, and grammar coverage
remains **214/83/131**.

## Dynamic-array `new[N]` positional patterns — 2026-10-25

A blocking assignment of the form `values = new[N]('{a, b, ...})` now lowers
for a finite scalar dynamic array when the literal size exactly matches a
pure positional pattern of integral scalar elements. The extractor samples the
new extent, materializes one flat cell per element, preserves source order, and
applies two-state x/z squashing at each destination cell. Keyed/default or
replicated patterns, effectful or aggregate elements, size mismatches,
declaration-time initializers, and scheduled forms remain loud because the
self-check state has no aggregate dynamic-array object.
The `dynamic_array_new_pattern` fixture and Lean receipt cover both two-state
and four-state cells, with extractor regressions pinning the refusal edges.

On the refreshed 22,050-path sv-tests-2 snapshot, clean files remain
**4,964 → 4,964** and partial files **17,020 → 17,020** (66 include skips);
`AssignmentExpression:target` falls **2,949 → 2,948**. Differential coverage grows
**182/177/0/5 → 183/178/0/5** with no disagreements, and grammar coverage
remains **214/83/131**.

## Dynamic arrays with fixed integral subarrays — 2026-10-25

A finite dynamic outer array whose elements are one or more fixed unpacked
dimensions of scalar or packed integral values now lowers through the existing
flat-cell representation. A literal `new[N]` samples the outer extent and
materializes every finite inner position in declared order, preserving
two-state zero initialization and ordinary constant-index reads and writes.
Dynamic inner dimensions, aggregate or nonintegral leaves, initializers on the
nested shape, and whole-array operations remain loud because the state has no
general nested dynamic-array object.
The `dynamic_array_fixed_subarrays` fixture exercises one- and two-level inner
dimensions, with extractor regressions pinning the dynamic-inner refusal.

On the same 22,050-path snapshot, clean files move **4,964 → 4,967** and
partial files **17,020 → 17,017** (66 include skips); `AssignmentExpression:target`
falls **2,949 → 2,944**, and `VariableSymbol:2state` falls **2,328 → 2,325**.
Differential coverage grows **183/178/0/5 → 184/179/0/5** with no
disagreements, and grammar coverage remains **214/83/131**.

## Finite literal array ordering — 2026-10-25

Blocking `sort()` and `rsort()` calls now lower for finite one-dimensional
integral arrays whose cells are available as a complete literal initializer or
as one sampled blocking literal write per cell. The extractor orders signed
literal cells, including unary-negative forms, and emits flat-cell writes for
the sorted result. Aliases, unknown or effectful values, duplicate writes,
whole-array uses, with clauses, and unsupported array shapes remain loud.
The `array_ordering_literals` fixture and Lean receipt cover ascending and
descending two-state and four-state cells, while extractor tests pin the
dynamic sampling and refusal edges.

On the refreshed 22,053-path snapshot, clean files move **4,967 → 4,970** and
partial files **17,017 → 17,016** (67 include skips); the leading
`AssignmentExpression:target` blocker is **2,945**. Differential coverage grows **184/179/0/5 → 185/180/0/5**
with no disagreements, and grammar coverage grows **214/83/131 → 214/85/129**.

## Finite literal string-key associative arrays — 2026-10-25

Associative arrays with a finite set of literal ASCII string keys now lower to
one flat scalar cell per observed key. Blocking writes and reads preserve
source order, empty keys, two-state defaults, and four-state values through the
existing assignment and expression nodes. Whole-array uses, dynamic or
non-ASCII keys, nonintegral elements, methods, and other associative index
types remain loud.
The `assoc_string_cells` fixture and Lean receipt cover static procedural cells,
including an empty key and four-state data, while extractor tests pin dynamic
and whole-array refusal edges.

On the refreshed 22,053-path snapshot, clean files move **4,970 → 4,979** and
partial files **17,016 → 17,007** (67 include skips); `AssignmentExpression:target`
falls **2,945 → 2,940**. Differential coverage grows **185/180/0/5 → 186/181/0/5**
with no disagreements, and grammar coverage grows **214/85/129 → 214/86/128**.

## Procedural fixed-array `reverse()` — 2026-10-25

A one-dimensional fixed unpacked integral array can now be reversed after a
complete blocking assignment-pattern initialization, after a copy from another
finite fixed array, and repeatedly in one linear process. The extractor replays
those source-ordered flat-cell writes and earlier reversals, preserving
four-state payloads and independent copies. Branches, loops, direct element
writes, dynamic or multidimensional arrays, nonliteral aggregate values, and
other array methods remain loud because the flat representation cannot sample
their runtime aggregate state soundly. The
`array_reverse_procedural` fixture and Lean receipt cover the procedural
pattern/copy/repeated-call path; extractor tests pin the branch and nonliteral
refusals.

On the fresh 22,053-path sv-tests-2 snapshot, clean files remain **4,979 →
4,979** and partial files **17,007 → 17,007** (67 include skips). The leading
`ExpressionStatement:CallExpression` blocker remains **2,942** because the
principal corpus witness also contains unsupported `sort()` calls. Differential
coverage grows **186/181/0/5 → 187/182/0/5** with no disagreements, and grammar
coverage remains **214/86/128**.

## Literal scalar mailbox FIFO `put()`/`get()` — 2026-10-25

A direct unbounded mailbox with a linear sequence of literal integral
`put()` calls now supports FIFO scalar `get()` calls. The extractor snapshots
messages in source order, lowers each get to the existing blocking scalar
assignment, and keeps `num()` exact after puts and gets. Bounded or aliased
mailboxes, dynamic messages, empty or width-mismatched gets, branching or looped
sequences, and other methods remain loud because the self-check state has no
mailbox object or scheduler.
The `mailbox_literal_fifo` fixture and Lean receipt cover literal, arithmetic,
and parameterized-int messages; extractor tests pin empty, dynamic, alias, and
branching refusals.

On the fresh 22,053-path sv-tests-2 snapshot, clean files move **4,979 →
4,990** and partial files **17,007 → 16,996** (67 include skips). The leading
call-statement blocker falls **2,942 → 2,926**, leaving
`AssignmentExpression:target` at **2,940** as the new leader. Differential
coverage grows **187/182/0/5 → 188/183/0/5** with no disagreements, and grammar
coverage remains **214/86/128**.

## Typed mailbox FIFO declarations — 2026-10-25

A procedural `mailbox#(T) mbx = new()` declaration now uses the existing
source-ordered scalar mailbox FIFO lowering when `T` is an admitted integral
message type. pyslang supplies an implicit default-size constructor argument,
so the extractor checks the source spelling and admits only the unbounded
`new()` form; bounded constructors and other initialized class handles remain
loud. `mailbox_typed_fifo` supplies the differential row and Lean receipt,
covering two matching `int` messages and the exact `num()` count.

On the refreshed 22,053-path snapshot, clean files move **4,992 → 4,993** and
partial files **16,994 → 16,993** (67 include skips). The leading
`AssignmentExpression:target` blocker remains **2,937**, while
`VariableSymbol:2state` falls **2,325 → 2,313** because the admitted typed
mailbox declaration shape occurs in 12 files. Differential coverage grows
**189/184/0/5 → 190/185/0/5** with no disagreements; grammar coverage grows
**214/86/128 → 216/88/128**.

DECIDED: the ten remaining sole `AssignmentExpression:target` files are live
continuous-driver, net-resolution, or whole-array cases. They require the
scheduler-owned driver state or aggregate storage and remain loud; the next
sound family is the leading `ExpressionStatement:CallExpression` blocker.

## Mailbox FIFO puts from pure scalar variables — 2026-10-25

The scalar mailbox snapshot now replays a direct integral variable message
when that variable has a source-ordered pure literal write before the `put()`.
This covers the §15.4.3 singular-expression rule without adding mailbox
storage: the snapshot substitutes the latest literal value, then existing FIFO
`get()` and `num()` lowering applies. Aliases, control-dependent or repeated
writes, nonliteral values, aggregate or handle messages, and other mailbox
methods remain loud. `mailbox_variable_fifo` supplies the differential row and
Lean receipt.

On the refreshed 22,053-path snapshot, clean files move **4,993 → 4,994** and
partial files **16,993 → 16,992** (67 include skips). The leading
`AssignmentExpression:target` blocker remains **2,937**; the
`ExpressionStatement:CallExpression` blocker falls **2,926 → 2,925**.
Differential coverage grows **190/185/0/5 → 191/186/0/5** with no
disagreements; grammar coverage remains **216/88/128**.

## Mailbox `num()` before the first operation — 2026-10-25

The source-ordered scalar mailbox snapshot now lowers `num()` immediately
after a direct unbounded `new()` to the exact zero count, while retaining the
existing count updates for later `put()` and `get()` calls. The dedicated
untouched-mailbox marker remains for the one-query shape; aliases, bounded
constructors, other methods, and dynamic activity stay loud. The
`mailbox_num_lifetime` fixture and Lean receipt cover the before/after counts.

On the refreshed 22,053-path snapshot, clean files move **4,994 → 4,995** and
partial files **16,992 → 16,991** (67 include skips). `CallExpression` falls
**2,904 → 2,903** while `AssignmentExpression:target` remains **2,937** and
`ExpressionStatement:CallExpression` remains **2,925**. Differential coverage
grows **191/186/0/5 → 192/187/0/5** with no disagreements; grammar coverage
remains **216/88/128**.

DECIDED: continue with the next sound sole `CallExpression` family after the
mailbox lifetime slice, preserving the capped validation and loud boundaries.

## Negative literal semaphore `try_get` normalization — 2026-10-25

The literal semaphore state snapshot now accepts the pinned `try_get(-1)`
compatibility form and normalizes its negative key count to one, matching the
self-check declaration for this simulator. The rule is limited to nonblocking
`try_get`; negative `put()` and `get()` calls, dynamic counts, aliases, and
other semaphore operations remain loud. `semaphore_negative_try_get` supplies
the differential row and Lean receipt.

On the refreshed 22,053-path snapshot, clean files move **4,995 → 4,996** and
partial files **16,991 → 16,990** (67 include skips). `CallExpression` falls
**2,903 → 2,902** while `AssignmentExpression:target` remains **2,937** and
`ExpressionStatement:CallExpression` remains **2,925**. Differential coverage
grows **192/187/0/5 → 193/188/0/5** with no disagreements; grammar coverage
remains **216/88/128**.

DECIDED: continue with the next sound sole `CallExpression` family, keeping
scheduler-dependent sampled-value functions and nondeterministic randomization
loud until their owning semantics exist.

## Parameterized packed-vector mailbox `try_put`/`try_get` — 2026-10-25

An unbounded `mailbox #(bit [7:0])` now admits source-ordered literal
`try_put` and `try_get` calls in expression assignments. `try_put` returns the
immediate success value, while `try_get` updates its scalar output argument
before publishing its return value; `num()` remains exact even when queried in
the surrounding condition. The recognizer checks the parameterized formal
width and keeps dynamic messages, aliases, unsupported methods, bounded
constructors, and width-mismatched messages or outputs loud. The
`mailbox_parameterized_packed_vector` fixture, Lean receipt, and focused
extractor tests cover the successful and refusal paths.

On the refreshed **22,053-path** sv-tests-2 snapshot, clean files move
**4,996 → 5,008** and partial files **16,990 → 16,978** (67 include skips).
`ExpressionStatement:CallExpression` falls **2,925 → 2,911** and
`CallExpression` falls **2,902 → 2,888**; `AssignmentExpression:target` remains
**2,937**. Differential coverage grows **193/188/0/5 → 194/189/0/5** with no
disagreements; grammar coverage grows **216/88/128 → 216/89/127**.

## Empty queue literal initializer `.size()` — 2026-10-25

An integral queue initialized by the empty queue literal now answers `.size()`
with the exact zero value, alongside the existing uninitialized queue and
empty-write cases. Nonempty initializers, later queue mutations, aliases, and
other queue observations remain loud because the flat self-check state carries
no queue object. `queue_empty_init` supplies the differential witness, while
the size-query regressions cover both procedural and module-scope declarations.

On the refreshed **22,053-path** sv-tests-2 snapshot, clean files move
**5,008 → 5,009** and partial files **16,978 → 16,977** (67 include skips).
`CallExpression` falls **2,888 → 2,887**; `ExpressionStatement:CallExpression`
remains **2,911** and `AssignmentExpression:target` remains **2,937**.
Differential coverage grows **194/189/0/5 → 195/190/0/5** with no
disagreements; grammar coverage remains **216/89/127**.

## `std::semaphore::try_get()` source-order scan — 2026-10-25

The literal semaphore `try_get` lowering now ignores comments and diagnostic
format strings while checking source-ordered constructor and method uses. This
admits the standard-library-qualified spelling in `std_semaphore_try_get` and
keeps the AST-backed constructor proof and literal balance unchanged. Aliases,
dynamic key counts, unsupported methods, and blocking operations remain loud.

On the refreshed **22,053-path** sv-tests-2 snapshot, clean files move
**5,009 → 5,010** and partial files **16,977 → 16,976** (67 include skips).
`CallExpression` falls **2,887 → 2,886** while `AssignmentExpression:target`
remains **2,937** and `ExpressionStatement:CallExpression` remains **2,911**.
Differential coverage grows **195/190/0/5 → 196/191/0/5** with no
disagreements; grammar coverage remains **216/89/127**.

## Empty queue `pop_front()` / `pop_back()` defaults — 2026-10-25

The self-check surface now evaluates a direct zero-argument `pop_front()` or
`pop_back()` on an uninitialized or empty-literal queue to the element type's
default value. Because the queue is empty, the operation leaves no represented
state and the existing `.size()` query remains exactly zero. Nonempty queues,
pushes, aliases, dynamic arguments, aggregate shapes outside the scalar
inventory, and discarded statement calls remain loud. `queue_empty_pop` covers
both directions and the extractor tests pin the masking and refusal boundary.

On the refreshed **22,053-path** sv-tests-2 snapshot, clean files move
**5,010 → 5,013** and partial files **16,976 → 16,973** (67 include skips).
`CallExpression` falls **2,886 → 2,877** while `AssignmentExpression:target`
remains **2,937** and `ExpressionStatement:CallExpression` remains **2,911**.
Differential coverage grows **196/191/0/5 → 197/192/0/5** with no
disagreements; grammar coverage remains **216/89/127**.

## Empty associative-array `num()` / `size()` — 2026-10-25

An untouched 2-state associative array now answers both `num()` and `size()`
with the exact zero count. The source scan allows only those zero-argument
queries after the declaration, so keyed writes, aliases, dynamic activity,
four-state arrays, and other methods remain loud. `assoc_empty_num` supplies
the differential witness and the extractor regressions pin comment masking and
the write refusal.

On the refreshed **22,053-path** sv-tests-2 snapshot, clean files move
**5,013 → 5,015** and partial files **16,973 → 16,971** (67 include skips).
`CallExpression` falls **2,877 → 2,875** while `AssignmentExpression:target`
remains **2,937** and `ExpressionStatement:CallExpression` remains **2,911**.
Differential coverage grows **197/192/0/5 → 198/193/0/5** with no
disagreements; grammar coverage remains **216/89/127**.

## Empty associative-array `first()` / `last()` — 2026-10-25

An untouched, uninitialized 2-state associative array now lowers `first(index)`
and `last(index)` to their exact signed 32-bit zero result when the index is a
direct named string or integral variable. The source-order check ignores
comments and strings and admits only further empty endpoint queries; writes,
aliases, four-state arrays, dynamic index expressions, and other associative
methods remain loud. The four sv-tests-2 endpoint files are clean, and the
`assoc_empty_endpoint` fixture supplies the module-scope differential and Lean
receipt.

On the refreshed **22,053-path** sv-tests-2 snapshot, clean files move
**5,015 → 5,019** and partial files **16,971 → 16,967** (67 include skips).
`CallExpression` falls **2,875 → 2,871** while `AssignmentExpression:target`
remains **2,937** and `ExpressionStatement:CallExpression` remains **2,911**.
Differential coverage grows **198/193/0/5 → 199/194/0/5** with no
disagreements; grammar coverage remains **216/89/127**.

## Untyped mailbox type-mismatch `try_get()` — 2026-10-25

An untyped mailbox with one literal message now lowers
`try_get(destination)` to the signed 32-bit negative result required by IEEE
1800-2023 §15.4.6 when the destination type is not equivalent to the queued
message type. The message is not consumed and no destination value is
published in the flat state. Typed mailboxes, aliases, dynamic messages,
multiple or reordered operations, and equivalent destination types remain
loud. The `mailbox_type_mismatch` fixture supplies the differential witness
and Lean receipt.

On the refreshed **22,053-path** sv-tests-2 snapshot, clean files move
**5,019 → 5,020** and partial files **16,967 → 16,966** (67 include skips).
`CallExpression` falls **2,871 → 2,870** while `AssignmentExpression:target`
remains **2,937** and `ExpressionStatement:CallExpression` remains **2,911**.
Differential coverage grows **199/194/0/5 → 200/195/0/5** with no
disagreements; grammar coverage remains **216/89/127**.

## Empty dynamic-array and string `$bits` queries — 2026-10-25

`$bits` now returns the exact signed 32-bit zero for an unallocated dynamic
array and for an empty string variable. The source scan allows only further
queries of the same empty value; allocated arrays, queue and associative
arrays, nonempty or written strings, real values, and type or expression forms
remain loud. The `empty_dynamic_bits` fixture supplies the differential
witness and Lean receipt, while the bit-query regressions pin the new dynamic
boundary.

On the refreshed **22,053-path** sv-tests-2 snapshot, clean files move
**5,020 → 5,024** and partial files **16,966 → 16,962** (67 include skips).
`CallExpression` falls **2,870 → 2,866** while `AssignmentExpression:target`
remains **2,937** and `ExpressionStatement:CallExpression` remains **2,911**.
Differential coverage grows **200/195/0/5 → 201/196/0/5** with no
disagreements; grammar coverage remains **216/89/127**.

## String `getc()` after a literal assignment — 2026-10-25

`string.getc(index)` now replays a direct blocking ASCII literal assignment
before the query and selects the latest assigned value. Negative and
out-of-range indices return the IEEE-mandated zero byte; dynamic strings,
aliases, non-ASCII writes, nonliteral indices, and other string operations
remain loud. The `string_getc_assignment` fixture supplies the differential
row and Lean receipt, while extractor regressions cover the latest-value and
dynamic-write boundaries.

On the refreshed **22,053-path** sv-tests-2 snapshot, clean files move
**5,024 → 5,031** and partial files **16,962 → 16,955** (67 include skips).
`CallExpression` falls **2,866 → 2,859** while `AssignmentExpression:target`
remains **2,937** and `ExpressionStatement:CallExpression` remains **2,911**.
Differential coverage grows **201/196/0/5 → 202/197/0/5** with no
disagreements; grammar coverage remains **216/89/127**.

## String literal queries across comments and escaped line continuations — 2026-10-25

The source-order history shared by literal string queries now scans a masked
code view: comments and quoted-string contents are blanked while offsets stay
stable. This keeps prose mentions of a receiver from becoming false runtime
uses and admits the standard combination of `.len()` and `.getc(index)` on a
proven ASCII literal, including a `\n` escape followed by a consumed
backslash-newline continuation. Dynamic writes, aliases, non-ASCII values,
unsupported methods, and other nonliteral observations remain loud. The
`string_query_lexing` fixture and extractor regressions cover the masking and
the exact six-character escaped value.

On the refreshed **22,053-path** sv-tests-2 snapshot, clean files move
**5,031 → 5,057** and partial files **16,955 → 16,929** (67 include skips).
`CallExpression` falls **2,859 → 2,833** while `AssignmentExpression:target`
remains **2,937** and `ExpressionStatement:CallExpression` remains **2,911**.
Differential coverage grows **202/197/0/5 → 203/198/0/5** with no
disagreements; grammar coverage remains **216/89/127**.

## Empty queue pops into integral unpacked structs — 2026-10-25

An empty `pop_front()` or `pop_back()` on an uninitialized queue now assigns an
untagged unpacked struct default field by field when every leaf is scalar or
packed integral. The lowering reuses the existing flattened struct cells and
therefore follows the §7.10.2.4 empty-pop result and §7.4.6 default
initialization without introducing queue storage. Mutated or aliased queues,
nonempty pops, aggregate fields, and scheduled forms remain loud. The
`queue_empty_pop_struct_default` fixture supplies the differential row and Lean
receipt.

On the refreshed **22,053-path** sv-tests-2 snapshot, clean files move
**5,057 → 5,058** and partial files **16,929 → 16,928** (67 include skips).
`AssignmentExpression:target` falls **2,937 → 2,936** while
`ExpressionStatement:CallExpression` remains **2,911**. Differential coverage
grows **203/198/0/5 → 204/199/0/5** with no disagreements; grammar coverage
remains **216/89/127**.

## Module-scope unbounded mailbox initializers — 2026-10-25

An unbounded `mailbox mbx = new()` declaration at module scope is now retained
as declaration metadata. The mailbox handle has no flat storage, while the
existing source-ordered literal FIFO recognizers model later `put()` and
`try_get()` operations. Bounded constructors, aliases, dynamic messages,
blocking or scheduled methods, and other initialized class handles remain
loud. The `mailbox_module_init` fixture supplies the differential row and Lean
receipt.

On the refreshed **22,054-path** sv-tests-2 snapshot, clean files move
**5,058 → 5,059** and partial files remain **16,928** (67 include skips).
`VariableSymbol:2state` falls **2,313 → 2,302**; `AssignmentExpression:target`
is **2,937**. Differential coverage grows **204/199/0/5 → 205/200/0/5** with
no disagreements; grammar coverage remains **216/89/127**.

## Discarded empty queue pops — 2026-10-25

The self-check surface now erases a direct `void'` call to `pop_front()` or
`pop_back()` when source-order analysis proves the queue is still empty. The
operation has no represented result or queue mutation, as required by IEEE
1800-2023 §§7.10.2.4–7.10.2.5. Nonempty and mutated queues, aliases, dynamic
receivers, and value-position calls remain loud. The
`queue_empty_pop_discarded` fixture supplies the differential row and Lean
receipt; extractor regressions cover both directions and the nonempty refusal.

On the refreshed **22,054-path** census, clean files move **5,059 → 5,061**
and partial files **16,928 → 16,926** (67 include skips).
`ExpressionStatement:CallExpression` falls **2,911 → 2,909** while
`AssignmentExpression:target` remains **2,937**. Differential coverage grows
**205/200/0/5 → 206/201/0/5** with no disagreements; grammar coverage is
**217/90/127**.

## Bounded `$isunbounded` queries — 2026-10-25

The self-check surface now lowers `$isunbounded(p)` to a one-bit zero when
`p` is a known bounded integral parameter, as specified by IEEE 1800-2023
§6.20.7. A direct integral literal follows the same pure path. Ordinary
variables, the special unbounded `$` value, and other parameter forms remain
loud because their binding is not represented in the flat state. The
`isunbounded_bounded` fixture supplies the differential row and Lean receipt;
extractor regressions pin literal, bounded-parameter, and variable refusals.

On the refreshed **22,054-path** census, clean files move **5,061 → 5,063**
and partial files **16,926 → 16,924** (67 include skips).
`CallExpression` falls **2,833 → 2,831** while `AssignmentExpression:target`
remains **2,937**. Differential coverage grows **206/201/0/5 → 207/202/0/5**
with no disagreements; grammar coverage remains **217/90/127**.

## Fixed-width real conversion `$bits` queries — 2026-10-25

The self-check surface now folds `$bits($realtobits(real_value))` and
`$bits($shortrealtobits(shortreal_value))` from the conversion result's fixed
64- or 32-bit width. The conversion remains pure metadata for this query and
does not expose real storage. Direct `$bits` of a named real, effectful
conversion operands, and other real calls remain loud. `real_bits_query` supplies
the differential witness and Lean receipt.

On the refreshed **22,054-path** census, clean files move **5,063 → 5,064**
and partial files **16,924 → 16,923** (67 include skips). `CallExpression` falls
**2,831 → 2,829** while `AssignmentExpression:target` remains **2,937** and
`ExpressionStatement:CallExpression` remains **2,909**. Differential coverage
grows **207/202/0/5 → 208/203/0/5** with no disagreements; grammar coverage
remains **217/90/127**.

## Dynamic-array `.size` without parentheses — 2026-10-25

The constant dynamic-array size lowering now accepts the IEEE 1800-2023 §5.13
omission of empty parentheses (`values.size`) as well as `values.size()`. A
single source-pure `new[N]` allocation is still required; later resizes,
mutation, aliases, and dynamic extents remain loud. The
`dynamic_array_size_property` fixture supplies the differential witness and
Lean receipt.

On the refreshed **22,054-path** census, clean files move **5,066 → 5,067**
and partial files **16,921 → 16,920** (67 include skips). `CallExpression`
remains **2,827** while `AssignmentExpression:target` remains **2,937** and
`ExpressionStatement:CallExpression` remains **2,909**. Differential coverage
grows **209/204/0/5 → 210/205/0/5** with no disagreements; grammar coverage
remains **217/90/127**.

## Predefined string macro `.len()` queries — 2026-10-25

The string-length lowering now accepts a string variable assigned a predefined
macro whose elaborated value is an ASCII literal. It matches that AST literal
assignment by source position, preserving the existing refusal for dynamic
assignments and other string methods. The `string_macro_len` fixture supplies
the triple-quoted macro and `` `__FILE__`` differential witness and Lean
receipt.

On the refreshed **22,054-path** census, clean files move **5,064 → 5,066**
and partial files **16,923 → 16,921** (67 include skips). `CallExpression` falls
**2,829 → 2,827** while `AssignmentExpression:target` remains **2,937** and
`ExpressionStatement:CallExpression` remains **2,909**. Differential coverage
grows **208/203/0/5 → 209/204/0/5** with no disagreements; grammar coverage
remains **217/90/127**.

## Enum `.name()` string values — 2026-10-25

The self-check tier now lowers `enum.name()` to an exact declaration-spelling
string value selected from the enum's declaration-order members. A value that
does not match a declared member returns the standard empty string. The
`enum_name_method` fixture exercises the rendered name; string comparisons,
dynamic string storage, and symbolic-mode enum calls remain loud.

On the refreshed **22,054-path** census, clean files move **5,067 → 5,077**
and partial files **16,920 → 16,910** (67 include skips). `CallExpression` falls
**2,827 → 2,799** while `AssignmentExpression:target` remains **2,937** and
`ExpressionStatement:CallExpression` remains **2,909**. Differential coverage
grows **210/205/0/5 → 211/206/0/5** with no disagreements; grammar coverage
remains **217/90/127**.

## Finite literal integral-key associative-array cells — 2026-10-25

Associative arrays with a finite set of literal integral keys now lower to one
flat scalar cell per observed key when their elements are scalar or packed
integral values. Blocking reads and writes preserve negative and positive
literal keys, source order, two-state defaults, and four-state values through
the existing assignment and expression nodes. Dynamic or unknown keys,
whole-array uses, methods, and aggregate elements remain loud. The
`assoc_integral_cells` fixture and Lean receipt cover the admitted cells, while
extractor tests pin dynamic-key and whole-array refusals.

On the refreshed **22,055-path** census, clean files move **5,077 → 5,084**
and partial files **16,910 → 16,904** (67 include skips). The leading
`AssignmentExpression:target` blocker remains **2,937** and
`ExpressionStatement:CallExpression` moves **2,909 → 2,910**. Differential
coverage grows **211/206/0/5 → 212/207/0/5** with no disagreements; grammar
coverage remains **217/90/127**.

## Nested multidimensional packed-array elements — 2026-10-25

Nested packed arrays now lower as contiguous integral vectors for constant
element reads and writes. Both canonical descending ranges and upward ranges
normalize their declared labels to the flat bit offset, and packed enum leaves
retain their packed element width. Dynamic selection of an element wider than
one bit remains loud because its stride cannot be represented by the current
dynamic select node. The `packed_array_multidim` fixture, generated envelope,
Lean receipt, and extractor regressions cover these cases.

On the refreshed **22,055-path** census, clean files move **5,084 → 5,126**
and partial files **16,904 → 16,862** (67 include skips). The leading
`AssignmentExpression:target` blocker falls **2,937 → 2,908**, while
`ExpressionStatement:CallExpression` remains **2,910**. Differential coverage
grows **212/207/0/5 → 213/208/0/5** with no disagreements; grammar coverage
remains **217/90/127**.

## Fixed-array `sort()` and `rsort()` after literal initialization — 2026-10-25

Fixed one-dimensional integral arrays now replay a complete blocking literal
pattern before `sort()` or `rsort()`. Repeated ordering calls consume the
previously sorted flat-cell state, and signed values use their declared
integral order. Unknown cells, aliases, dynamic or multidimensional arrays,
and `with` clauses remain loud. The `fixed_array_sort` fixture, generated
envelope, Lean receipt, and extractor regressions cover the admitted and
refused shapes.

On the refreshed **22,055-path** census, clean files move **5,126 → 5,127**
and partial files **16,862 → 16,861** (67 include skips).
`ExpressionStatement:CallExpression` falls **2,910 → 2,909**, while
`AssignmentExpression:target` remains **2,908**. Differential coverage grows
**213/208/0/5 → 214/209/0/5** with no disagreements; grammar coverage remains
**217/90/127**.

## Task-selected `$swriteb`/`$swriteo`/`$swriteh` packed writes — 2026-10-25

Direct packed-integral destinations now lower the IEEE 1800-2023 §21.3.3
task-selected binary, octal, and hexadecimal output forms when their source is
an earlier blocking literal integral assignment. Radix groups preserve the
four-state `x`/`z` spelling and right-align their rendered bytes in the packed
destination. String destinations, dynamic sources, timing controls, and other
task forms remain loud. `swrite_default_radix` is the differential and Lean
receipt fixture, with extractor regressions for the admitted rendering and its
dynamic-source boundary.

The refreshed **22,055-path** census moves **5,127 → 5,128 clean** and
**16,861 → 16,860 partial** (67 include skips). The leading
`ExpressionStatement:CallExpression` blocker falls **2,909 → 2,908**, while
`AssignmentExpression:target` remains **2,908**. Differential coverage grows
**214/209/0/5 → 215/210/0/5** with no disagreements; grammar coverage remains
**217/90/127**.

## Constant nested packed scalar selections — 2026-10-25

Constant element and part selections through two or more packed dimensions now
flatten to one offset in the root integral vector for both reads and writes.
Declared descending and ascending labels compose in source order, while
dynamic labels and aggregate or member receivers remain loud. The
`packed_nested_scalar_select` fixture supplies the differential row, generated
envelope, and Lean receipt; extractor regressions cover scalar and part writes,
ascending ranges, four-state `x`, and dynamic-index refusal.

The refreshed **22,055-path** census moves **5,128 → 5,130 clean** and
**16,860 → 16,858 partial** (67 include skips). The
`AssignmentExpression:target` blocker falls **2,908 → 2,905**, while
`ExpressionStatement:CallExpression` remains **2,908**. Differential coverage
grows **215/210/0/5 → 216/211/0/5** with no disagreements; grammar coverage
remains **217/90/127**.

## Static-scope `$sdf_annotate` calls — 2026-10-25

The self-check surface now erases `$sdf_annotate` when its SDF filename is a
literal and its optional module scope is a static elaborated scope. The
time-zero envelope has no timing-annotation state, so this form has no modeled
effect; dynamic filenames, nonstatic scopes, nonempty config files, and other
optional forms remain loud. The `sdf_static_scope` fixture supplies the
differential row and Lean receipt, with extractor coverage for the static-scope
boundary.

The refreshed **22,055-path** census moves **5,130 → 5,132 clean** and
**16,858 → 16,856 partial** (67 include skips). The
`ExpressionStatement:CallExpression` blocker falls **2,908 → 2,778** and is
overtaken by `AssignmentExpression:target` at **2,905**; 130 corpus call sites
match this static-scope form and two of their files become clean. Differential
coverage grows **216/211/0/5 → 217/212/0/5** with no disagreements; grammar
coverage remains **217/90/127**.

## Literal wired-net resolution — 2026-10-26

Literal continuous drivers of `wand`, `wor`, `triand`, and `trior` nets now
resolve at time zero with the IEEE wired-AND and wired-OR four-state tables.
The extractor folds complete literal driver sets into one flat net write;
dynamic, strengthened, and mixed driver sets remain loud. The
`wired_net_resolution` fixture supplies the differential row and Lean receipt,
and extractor regressions cover vector resolution and dynamic-driver refusal.

The refreshed **22,055-path** census moves **5,132 → 5,166 clean** and
**16,856 → 16,822 partial** (67 include skips). The
`AssignmentExpression:target` blocker falls **2,905 → 2,875**;
`CallExpression` remains **2,801** and `ExpressionStatement:CallExpression`
remains **2,778**. Differential coverage grows **217/212/0/5 → 218/213/0/5**
with no disagreements; grammar coverage remains **217/90/127**.

## Literal-bound associative-array keys — 2026-10-26

Finite associative-array lowering now resolves a selector through a named
string or integral variable when its declaration initializer is a literal and
the variable has no later assignment. The existing flat scalar cell is reused
for the proven key, including compound writes; dynamic or rebound selectors,
whole-array uses, and aggregate elements remain loud. The `assoc_bound_key`
fixture supplies the differential row and Lean receipt, with extractor
regressions for both key kinds and the rebind boundary.

The refreshed **22,055-path** census remains **5,166 clean** and **16,822
partial** (67 include skips), with `AssignmentExpression:target` remaining
**2,875**. Differential coverage grows **218/213/0/5 → 219/214/0/5** with no
disagreements; grammar coverage remains **217/90/127**.
## Literal-bound real-to-bits conversions — 2026-10-26

`$realtobits` and `$shortrealtobits` now consume a named `real` or `shortreal`
when its declaration initializer or each preceding direct blocking assignment
is a finite literal outside control flow. The extractor preserves the exact
IEEE-754 double or single bit pattern while keeping dynamic reads, arithmetic,
nonblocking writes, and control-dependent rebinding loud. The
`literal_bound_real_bits` fixture supplies the differential row and Lean
receipt, with regressions for declaration and assignment bindings and the
rebind boundary.

On the refreshed **22,056-path** sv-tests-2 snapshot, clean files move
**5,200 → 5,207** and partial files **16,789 → 16,782** (67 include skips).
`CallExpression` falls **2,796 → 2,780**. Differential coverage grows
**231/226/0/5 → 232/227/0/5** with no disagreements; grammar coverage remains
**217/90/127**.

## Immutable literal variables as continuous net sources — 2026-10-26

Continuous assignment now accepts a whole net driven by a variable whose
declaration initializer is a finite integral literal and which has no
procedural writes. The source is folded to the existing time-zero literal
driver, preserving the flat net value without inventing a live driver. Dynamic
sources, aggregate targets, rebinding, and multi-driver resolution remain
loud. The `continuous_bound_literal` fixture supplies the differential row
and Lean receipt, with extractor regressions for the immutable and rebind
boundaries.

## Disjoint fixed-array slice copies — 2026-10-26

Blocking assignment between non-overlapping constant slices of one finite
unpacked integral array now expands to cellwise reads and writes. The
expansion preserves source values because no destination cell aliases a
source cell; overlapping slices and dynamic or aggregate forms remain loud.
The `fixed_array_disjoint_slice_copy` fixture supplies the differential row
and Lean receipt, with extractor regressions for the admitted and overlap
boundaries.

## Whole fixed-array copies from wire arrays — 2026-10-26

Blocking assignment from an equal-length finite unpacked integral wire array
now expands to cellwise reads and writes. The source cells are already
resolved by the existing net lowering, so this preserves the wire values
without inventing aggregate storage. Dynamic or mismatched arrays and other
aggregate forms remain loud. The `fixed_array_net_copy` fixture supplies the
differential row and Lean receipt, with extractor regressions for the wire
source and mismatch boundary.

On the refreshed **22,056-path** census, clean files move **5,207 → 5,209**
and partial files **16,782 → 16,780** (67 include skips). The
`AssignmentExpression:target` blocker falls **2,861 → 2,860**,
`ExpressionStatement:CallExpression` falls **2,776 → 2,775**, and
`ElementSelectExpression:source-type` falls **500 → 497**. Differential
coverage grows **238/233/0/5 → 239/234/0/5** with no disagreements; grammar
coverage remains **217/90/127**.

## Destructive finite dynamic-array reinitialization — 2026-10-26

Two plain positive constant allocations of one finite scalar dynamic array now
admit the IEEE destructive reinitialization rule. The second `new[N]` drops the
old cells and publishes fresh type-default cells, while resize-copy,
self-growth, zero-sized, dynamic-sized, and third allocations remain loud. The
`dynamic_array_reinitialization` fixture supplies the differential row and Lean
receipt, with extractor coverage for the reset cells and the existing resize
boundaries.

On the refreshed **22,056-path** census, clean files move **5,209 → 5,210**
and partial files **16,780 → 16,779** (67 include skips). The
`AssignmentExpression:target` blocker falls **2,860 → 2,857** and
`CallExpression` **2,780 → 2,778**. Differential coverage grows
**239/234/0/5 → 240/235/0/5** with no disagreements; grammar coverage remains
**217/90/127**.

## Constant out-of-bounds unpacked-array reads — 2026-10-26

Constant reads beyond a finite unpacked integral array now lower to the IEEE
element default: all zeroes for a two-state element and all x for a four-state
element, including an enum's four-state base type. Dynamic indices, packed or
scalar diagnostics, aggregate leaves, and dynamic arrays remain loud. The
`array_oob_reads` fixture supplies the differential row and Lean receipt, with
extractor regressions for both state kinds and the scalar boundary.

On the refreshed **22,056-path** census, clean files move **5,210 → 5,215**
and partial files **16,779 → 16,774** (67 include skips).
`ElementSelectExpression:source-type` falls **495 → 490**. Differential
coverage grows **240/235/0/5 → 241/236/0/5** with no disagreements; grammar
coverage remains **217/90/127**.

## Direct indexing of literal ASCII strings — 2026-10-26

Constant indexing of a source-pure ASCII string now lowers to its byte value,
with the IEEE zero result for negative and out-of-range indices. Dynamic
indices, aliases, non-ASCII or nonliteral writes, and element writes remain
loud. The `string_index` fixture supplies the differential row and Lean
receipt, with extractor tests for literal history and each refusal boundary.

On the refreshed **22,056-path** census, clean files move **5,215 → 5,227**
and partial files **16,774 → 16,762** (67 include skips).
`ElementSelectExpression:source-type` falls **490 → 479**. Differential
coverage grows **241/236/0/5 → 242/237/0/5** with no disagreements; grammar
coverage remains **217/92/125**.

## Single literal initial-write continuous sources — 2026-10-26

A continuous scalar net driver may now fold a variable RHS when that variable
has exactly one direct blocking literal assignment in an `initial` block, with
no declaration initializer or other writes. This is lowered to the existing
time-zero literal driver, so the self-check observes the source value without
introducing a live scheduler driver. Dynamic, control-dependent, multiply
written, and nonliteral sources remain loud. The
`continuous_history_literal` fixture supplies the differential row and Lean
receipt, with extractor regressions for the one-write and multiple-write
boundaries.

On the refreshed **22,056-path** census, clean and partial counts remain
**5,227 / 16,762** (67 include skips), and `AssignmentExpression:target`
remains **2,857**. Differential coverage grows **242/237/0/5 → 243/238/0/5**
with no disagreements; grammar coverage remains **217/92/125**.

## Whole bounded multidimensional fixed-array copies — 2026-10-26

Assignments between distinct bounded multidimensional unpacked arrays with
integral leaves now expand in declaration order to the existing flat vector
cells. Equal ordinal shapes may use different declared index labels, matching
SystemVerilog's assignment-compatible unpacked arrays. Self-copies,
mismatched dimensions, dynamic or aggregate leaves, and effectful sources
remain loud. The `fixed_array_nested_copy` fixture supplies the differential
row and Lean receipt, with extractor regressions for ordinal mapping and the
refusal boundaries.

The refreshed **22,058-path** census remains **5,227 clean / 16,764 partial**
(67 include skips), with `AssignmentExpression:target` at **2,857** because
the remaining corpus target rows require other aggregate or scheduler state.
Differential coverage grows **243/238/0/5 → 244/239/0/5** with no
disagreements; grammar coverage remains **217/92/125**.

## Constant multidimensional subarray copies — 2026-10-26

A constant prefix selection of a bounded multidimensional unpacked integral
array may now copy into a distinct flat fixed array in declaration order. The
existing cell expansion supplies the complete source row; dynamic selectors,
overlapping aliases, mismatched extents, aggregate leaves, and effectful
sources remain loud. The `fixed_array_subarray_copy` fixture supplies the
differential row and Lean receipt, with extractor regressions for the selected
row and refusal boundaries.

The refreshed **22,058-path** census remains **5,227 clean / 16,764 partial**
(67 include skips), with `AssignmentExpression:target` at **2,857** because
the remaining corpus target rows require other aggregate or scheduler state.
Differential coverage grows **244/239/0/5 → 245/240/0/5** with no
disagreements; grammar coverage remains **217/92/125**.

## Dynamic outer multidimensional subarray copies — 2026-10-26

A single dynamic outer selector may now copy a distinct flat fixed-array row
into a bounded multidimensional unpacked integral array. The extractor lowers
the finite outer range to mutually exclusive `===` branches and expands each
suffix cell in declaration order, so the existing flat state remains the only
storage representation. Multiple dynamic selectors, aliases, mismatched
shapes, aggregate leaves, timed assignments, and effectful sources remain
loud. The `nested_fixed_array_dynamic_subarray_copy` fixture supplies the
differential row and Lean receipt, with extractor regressions for cell order
and the shape refusal.

The refreshed **22,058-path** census remains **5,227 clean / 16,764 partial**
(67 include skips), with `AssignmentExpression:target` at **2,857**.
Differential coverage grows **245/240/0/5 → 246/241/0/5** with no
disagreements; grammar coverage remains **217/92/125**.

## Dynamic inner-prefix multidimensional subarray copies — 2026-10-26

The same finite branch expansion now admits one dynamic selector after a
constant prefix of a bounded multidimensional unpacked integral array. A form
such as `cube[0][index] = row` copies a distinct flat row into the omitted
suffix cells in declaration order, using only the existing flat storage. The
multiple-dynamic, aliasing, shape-mismatch, aggregate, timed, and effectful
boundaries remain loud. The `nested_fixed_array_dynamic_inner_subarray_copy`
fixture supplies the differential row and Lean receipt, with extractor
regressions for the inner-prefix branch mapping.

The refreshed **22,058-path** census remains **5,227 clean / 16,764 partial**
(67 include skips), with `AssignmentExpression:target` at **2,857**.
Differential coverage grows **246/241/0/5 → 247/242/0/5** with no
disagreements; grammar coverage remains **217/92/125**.

## Dynamic multidimensional subarray source reads — 2026-10-26

A bounded multidimensional unpacked integral source with one dynamic selector
may now be read into a distinct flat fixed-array row. The extractor lowers
the finite selector range to mutually exclusive `===` branches and expands
the omitted suffix cells in declaration order, so the interpreter continues
to use only the existing scalar-cell state. Multiple dynamic selectors,
shape mismatches, aliases, aggregate leaves, timed assignments, and
effectful sources remain loud.

`nested_fixed_array_dynamic_subarray_read_copy` supplies the differential
row and Lean receipt. The current 22,058-path census remains 5,227 clean and
16,764 partial with 67 include skips; differential coverage is 248 rows,
243 matches, zero disagreements, and 5 recorded refusals, while the grammar
census remains 217 witnesses (92 MATCH, 125 REFUSE).

## Dynamic packed slices inside fixed-array cells — 2026-10-26

Dynamic indexed part-selects inside a constant bounded-array cell now use the
existing flat selected-read and selected-write nodes. For a descending packed
cell such as `bit [3:0][7:0] joe [0:9]`, a runtime base is multiplied by the
inner element width; `-:` additionally converts its high endpoint to the
selected-write convention. The fixture exercises both directions and a
runtime readback. Ascending packed ranges, dynamic widths, aggregate cells,
and effectful bases remain loud.

The 22,058-path corpus remains **5,227 clean / 16,764 partial** with 67
include skips and `AssignmentExpression:target` at **2,857**. Differential
coverage moves **248/243/0/5 → 249/244/0/5** with no disagreements; grammar
coverage remains **217/92/125**.

## Fixed struct-array `sort`/`rsort` with `(item.field)` — 2026-10-27

One-dimensional fixed unpacked arrays of shallow structs now lower `sort` and
`rsort` calls with a direct scalar `item.field` key. The extractor replays
source-ordered blocking literal pattern or field writes, orders complete
records by the declared integral field, and emits flattened writes for every
field, including repeated ordering calls. Computed, dynamic, queue,
nested-aggregate, unknown, aliased, timed, and value-position forms remain
loud because the self-check state has no general aggregate object or ordering
oracle. The `struct_array_ordering_with_field` fixture and Lean receipt cover
ascending and descending record order; extractor regressions pin the key and
aggregate refusal edges.

On the refreshed **22,059-path** sv-tests-2 census, clean files move
**5,287 → 5,292** and partial files **16,705 → 16,700** (67 include skips).
The leading `ExpressionStatement:CallExpression` blocker falls
**2,746 → 2,741**. Differential coverage grows **308/303/0/5 → 309/304/0/5**
with no disagreements; grammar coverage remains **218/96/122**.

## Finite literal mailbox FIFO loops — 2026-10-27

The mailbox scalar snapshot now admits a finite source-pure pair of
procedural `for` loops with one direct unbounded mailbox handle. Each loop has
a literal nonnegative start, a literal upper bound, and a unit increment; its
body is limited to scalar blocking literal assignments, FIFO `put()`/`get()`
calls, and conditions decided from the replayed scalar environment. The
extractor unrolls those iterations and carries the exact queue across the
enclosing block, so the flat self-check state still has no mailbox object.
Dynamic bounds, aliases, control-dependent writes, timing, nonintegral or
aggregate messages, and other mailbox methods remain loud. The
`mailbox_literal_loop_fifo` fixture and Lean receipt cover ten puts followed by
ten FIFO gets.

On the refreshed **22,059-path** sv-tests-2 census, clean files move
**5,293 → 5,294** and partial files **16,699 → 16,698** (67 include skips).
The `ExpressionStatement:CallExpression` blocker falls **2,740 → 2,739**.
Differential coverage grows **310/305/0/5 → 311/306/0/5** with no
disagreements; grammar coverage remains **218/96/122**.

## Fixed struct-array `sort` with packed tuple keys — 2026-10-27

The same one-dimensional fixed unpacked struct-array lowering now admits a
direct packed concatenation key with an explicit iterator, such as
`values.sort(x) with ({x.blue, x.green})`. Each field's known raw bits forms
one lexicographic component of the packed key, and complete records are
replayed in source order before flattened writes are emitted. Computed,
duplicate, dynamic, queue, nested-aggregate, unknown, aliased, timed, and
value-position keys remain loud. The `struct_array_ordering_with_tuple`
fixture and Lean receipt cover the ascending two-field order.

On the refreshed **22,059-path** sv-tests-2 census, clean files move
**5,292 → 5,293** and partial files **16,700 → 16,699** (67 include skips).
The leading `ExpressionStatement:CallExpression` blocker falls
**2,741 → 2,740**. Differential coverage grows **309/304/0/5 → 310/305/0/5**
with no disagreements; grammar coverage remains **218/96/122**.

## Literal queue to fixed-array copies — 2026-10-27

The assignment surface now expands a source-pure scalar-literal queue into a
same-count fixed unpacked integral array, preserving left-to-right element
correspondence through the existing flat cells. Queue mutations, aliases,
aggregate elements, size mismatches, timed/nonblocking forms, and continuous
driver resolution remain loud. The `queue_fixed_array_copy` fixture and Lean
receipt provide the differential witness.

The refreshed 22,059-path census moves **5,303 → 5,304 clean** and
**16,689 → 16,688 partial** (67 include skips); the
`AssignmentExpression:target` wall falls **2,845 → 2,844**. Differential
coverage is **318 rows / 312 matches / 0 disagreements / 6 recorded
refusals**, and grammar coverage remains **218 / 97 / 121**.

## Multidimensional fixed-array `foreach` — 2026-10-27

Finite multidimensional unpacked integral arrays now admit `foreach` loops
when every dimension is explicitly bound. The extractor lowers the loop to
the existing ordinal `For` form and expands dynamic element reads and writes
to mutually exclusive conditions over flat leaf cells. Incomplete dimensions,
dynamic or queue arrays, aggregate leaves, and effectful selectors remain
loud. The `foreach_nested` fixture and Lean receipt cover a two-by-three array
sum and the dynamic selector path.

The pinned 22,065-file census remains **5,401 clean / 16,597 partial** with 67
include skips; the committed `ForeachLoopStatement:array` count remains 123
because the unavailable corpus snapshot cannot be rerun here. Differential
coverage grows **334/328/0/6 → 335/329/0/6** with no disagreements, and grammar
coverage remains **218/97/121**.

## Unreferenced subroutine declarations — 2026-10-27

Module-scope functions and tasks with no elaborated `CallExpression.subroutine`
reference are now erased as inert declarations. Their bodies cannot execute
merely because they are declared, so this does not add callable frames or
scheduler state. Referenced, recursive, receiver, DPI, and effectful-call
subroutines remain loud. The `unused_subroutines` fixture and Lean receipt
cover an uncalled effectful task and function; `docs/sv-subroutines.md` records
the retained boundary.

The pinned 22,065-file census remains **5,401 clean / 16,597 partial** with 67
include skips because the external corpus checkout is unavailable; the
committed `SubroutineSymbol:Subroutine` count remains 1,634. Differential
coverage grows **335/329/0/6 → 336/330/0/6** with no disagreements, and grammar
coverage remains **218/97/121**.

## Unreferenced package subroutine declarations — 2026-10-27

Package functions and tasks with no elaborated `CallExpression.subroutine`
target anywhere in the compilation are now erased as inert declarations. The
identity scan covers calls from modules, imports, other packages and recursive
bodies, so called and recursive package routines remain at the existing
`Package:Subroutine` boundary. No package callable frame, constant-function
evaluator, DPI ABI or scheduler state is introduced. The
`package_unused_subroutines` fixture and Lean receipt cover an effectful task
and function that are never called.

The pinned 22,065-file census remains **5,401 clean / 16,597 partial** with 67
include skips because the external corpus checkout is unavailable; the
committed `SubroutineSymbol:Subroutine` count remains 1,634. Differential
coverage grows **336/330/0/6 → 337/331/0/6** with no disagreements, and grammar
coverage remains **218/97/121**.

## Fixed-array assignment-pattern self-alias snapshots — 2026-10-27

The legacy assignment-pattern lowering now admits a one-dimensional fixed
unpacked integral array whose pure positional RHS reads the same destination
cells. It emits one `LocalDecl` snapshot per RHS element before any flattened
cell store, so `values = '{values[1], values[0]}` produces the source-defined
swap rather than observing an earlier lowered write. Nested arrays,
dynamic/queue/associative storage, effectful expressions, width mismatches and
other aggregate aliases remain loud. The existing `assignment_patterns/self_alias`
fixture and Lean receipt cover `self 7 3`.

The pinned 22,065-file census remains **5,401 clean / 16,597 partial** with 67
include skips because the external corpus checkout is unavailable; the
committed `AssignmentExpression:target` count remains 2,847. Differential
coverage grows **337/331/0/6 → 338/332/0/6** with no disagreements, and grammar
coverage remains **218/97/121**.

## Exact fixed-array blocking self-copies — 2026-10-27

An exact whole-array blocking assignment to the same one-dimensional fixed
unpacked integral array now lowers to `Empty`, since each source cell is
already the corresponding destination cell. Sliced or overlapping copies,
nonblocking and timed forms, dynamic or aggregate storage, and effectful
sources remain loud; no aggregate snapshot or scheduler state is introduced.
The `fixed_array_self_copy` fixture and Lean receipt cover `selfcopy 3 7`.

The pinned 22,065-file census remains **5,401 clean / 16,597 partial** with 67
include skips because the external corpus checkout is unavailable; the
committed `AssignmentExpression:target` count remains 2,847. Differential
coverage grows **338/332/0/6 → 339/333/0/6** with no disagreements, and grammar
coverage remains **218/97/121**.

## Zero-size dynamic-array declarations — 2026-10-27

Module and procedural declarations initialized by `new[0]` or an empty
assignment pattern now lower to inert metadata for both 2-state and 4-state
element types. An empty dynamic array has no flat cells to initialize, so this
uses the existing `Empty` self-check node without inventing dynamic storage.
Nonzero allocations, effectful initializers, later resizes, and element reads or
writes remain loud. The `dynamic_array_empty_decl` fixture and Lean receipt
cover all four admitted declaration forms.

The pinned 22,065-file census remains **5,401 clean / 16,597 partial** with 67
include skips because the external corpus checkout is unavailable; the committed
`VariableSymbol:2state` count remains 2,118. Differential coverage grows
**339/333/0/6 → 340/334/0/6** with no disagreements, and grammar coverage
remains **218/97/121**.

## Discarded pure integral operands for real conversions — 2026-10-28

The legacy self-check tier now admits discarded `$itor`, `$bitstoreal`, and
`$bitstoshortreal` calls when their integral operands are source-pure. A read,
literal, or pure integral expression still has to be evaluated, but its opaque
real result has no represented state once discarded. `$bitstoreal` accepts only
64-bit source expressions and `$bitstoshortreal` only 32-bit expressions;
pyslang's implicit formal conversion is not allowed to hide a wrong-width
source. Incrementing or other effectful operands, timing, unsupported
aggregates, and value-position calls remain loud. The
`pure_integral_real_conversions` fixture and extractor regressions are the
acceptance evidence. Differential coverage grows **415/409/0/6 →
416/410/0/6** with no disagreements, and grammar coverage grows
**218/106/112 → 218/107/111**.

## Discarded pure floating math — 2026-10-28

The legacy self-check tier admits discarded calls in the pure IEEE floating
math family. It reuses the established operand purity checker, so literals,
read-only names, and nested math calls have no represented state after their
opaque real result is discarded. Effectful, timed, unsupported, and
value-position forms remain loud. The `discarded_pure_floating_math` fixture
is the acceptance witness.

## Discarded pure real-to-bits conversions — 2026-10-28

The legacy self-check tier now erases discarded `$realtobits` and
`$shortrealtobits` calls when their real operands are source-pure. The shared
floating expression walk admits read-only names, literals, and nested pure math
calls while retaining the exact 64-bit and 32-bit unsigned result boundaries.
Effectful, timed, unsupported, and value-position forms remain loud. The
`discarded_pure_real_to_bits` fixture and extractor regressions are the
acceptance evidence.

## Discarded pure `$rtoi` conversions — 2026-10-28

The legacy self-check tier now erases discarded `$rtoi` calls with source-pure
real operands. The shared floating expression walk admits reads, literals, and
nested pure math calls while preserving the signed 32-bit conversion boundary.
Effectful, timed, unsupported, and value-position forms remain loud. The
`discarded_pure_rtoi` fixture and extractor regressions are the acceptance
evidence.

## Concatenated continuous-assignment targets in the comb settle theorem — 2026-10-27

The Design2 combinational settle theorem (`LeanModels/Sv/Comb2Base`,
`Comb2Sound`, `Comb2Term`, `Comb2`) now admits continuous assigns whose target
is a concatenation — `assign {cout, s} = a + b + cin;`, nested ones included —
of leaves (whole signals, constant slices, constant-literal element selects).
A target's static write windows are a list (`Lhs2.windows?` / `Lhs2.wins`,
MSB-first), each placed at its bit offset in the concatenated value
(`Win.placed`); one process's effect is `combWrite`, the right-hand side
resized to the target's total width and written slice by slice, proved equal
on shaped states to the interpreter's own path (`resolveConcatLhs2_of_windows?`,
`writeConcatLhs2_eq`). The profile gains one obligation, `selfDisjoint` (a
target's windows are pairwise disjoint); `CombEqs` says each placed window
holds its slice of the resized right-hand side, and `Writes`/`Acyclic` range
over every window. Settle soundness, termination, the `⊨₂` introductions and
the leaf read-backs keep their statements; the ripple-adder proof changes by
six one-line edits (window membership by `simp`, a one-element window list)
plus the new `selfDisjoint` field. New
read-backs `CombEqs.concat_part` / `CombEqs.concat_part_ident`.

`LeanModels/Sv/Comb2ConcatExample.lean` proves the one-line adder correct for
every width `N` — the same statement as `ripple_add`'s gate-level proof — and
a nested `{y[3:2], {z, y[1:0]}} = x` target, with `run2` `#guard`s under both
schedules. Differential rows `concat_add` (`N` = 4, 1, 8) and `concat_split`
(slices, a bit-select rotation, zero-extension, truncation) match Icarus;
`Examples/system-verilog/sem2/concat_add/agree.lean` checks that the SV source
instantiates to exactly the proved design family at `N` = 1, 2, 4, 8, 32.
Dynamic-index leaves stay off-profile, and `always_comb` processes remain
outside the comb profile.

## Nested packed-array selects (`ArraySel`) — 2026-10-27

sv-0.2 symbolic mode now admits multi-dimensional packed arrays with nested
selects whose labels are elaboration-time constants — `pp[i][j]`,
`s[i-1][j+1]`, row reads `pp[i]`, row part-selects `s[N-1][N:1]`, indexed
parts `x[i*W +: W]` — as continuous and procedural TARGETS and in
expressions, over any number of dimensions and over ascending, descending
and non-zero-based ranges whose bounds may depend on parameters. The
extractor emits each chain as ONE `ArraySel` node with the raw declared
labels (`docs/sv-envelope-schema.md`, "Packed-array select paths"); the
`IEnv` of `instantiate2` carries every declaration's dimensions EVALUATED
ONCE in the declaration scope (`IEnv.dims`, built by `dimTable` from
`PDesign.packedDims` before generate expansion, so a genvar that reuses a
parameter's name cannot change an array's geometry — found by independent
review, pinned by the `array_gvshadow*` rows), and `Param2.lean` lowers a chain to
one flat window of the declared vector after normalizing each label against
its own dimension and checking each dimension's range (IEEE 1800-2023
§7.4.2, §7.4.6, §11.5.1). `Sem2` is unchanged: an in-range select is a
`slice`, an out-of-range element select reads x and writes the zero-width
window (no-op), a partial part select reads x in exactly its out-of-range
bits and, as a target, writes the in-range bits of an msb-side overhang
(an lsb-side overhang on a target is loud). Previously admitted selects keep
their legacy nodes byte-for-byte (all 77 reproducible sv-0.2 envelopes
re-extract identically); two legacy default-folds that were wrong away from
the default parameters (`u[5]` over `[7:L]`, `x[4 +: N]`) now take the new
path, and a dynamic inner index on a 3-D array, which the legacy encoding
sized as one bit, is now loud.

Proof handles (`LeanModels/Sv/Gen2.lean`, "Packed-array select paths at
symbolic parameters"): `PDesign.dimTable_lookup_of`/`evalDims_cons_of` give
an instantiated environment's geometry entry, `arrayDims_of` reads it,
`walkIndices_cons_of`/`walkIndices_desc0_cons` walk the labels
(`[m:0]` has label = offset and `m + 1` elements), and
`arrayElemRead_of_inRange`/`arrayElemTarget_of_inRange` (and the part twins)
give the flat `slice`. `Examples/system-verilog/mul2d/gen.lean` proves, for
every `N ≥ 1`, the whole instantiated process list of the 2-D array
multiplier `mul2d.sv` (`mul2d_processes`, the `ripple_processes` twin), in
particular that its partial-product generate block instantiates to the cells
`pp[i*N+j] = a[j] & b[i]` (`mul2d_pp_expand`, `mul2d_pp_instantiated`) and
that `s[i-1][j+1]` reads the 1-bit window at `(i-1)*(N+1) + (j+1)`. The `Gen2.except_ok_bind` /
`except_error_bind` lemmas about core `Except` are no longer global `simp`
lemmas (local to `Gen2.lean`, passed explicitly by `sv2_inst_simp` and the
ripple-adder instantiation proofs).

Differential rows (Icarus 12.0): `mul2d_n4_all` (all 256 products plus four
x/z cycles, sampling every internal 2-D array), `mul2d_n{1,2,3}_all`,
`mul2d_n5_sample`; `array_ranges` at three parameter points (ascending
outer, non-zero-based inner, `+:`/`-:` parts), `array_3d`, `array_oob`
(selects past the end of the last element), `array_param_labels` at three
parameter points, `array_gvshadow` at three parameter points (genvars named
like the parameters in a declared range; read and target) — all match.
`array_oob_inner` and `array_oob_part` are declared disagreements: Icarus
12.0 and Yosys 0.53 linearize an out-of-range INNER index (`m[0][4]` reads
`m[1][0]`) and a part or indexed part overhanging an inner dimension of a
non-last element (`m[0][5:3]`, `q[1][-1 +: 2]`, the write `w[0][5:2] = a`),
while the LRM and slang check each dimension
(`docs/sv-oracle-disagreements.md`, "Linearized packed-array indices").
Out of tier, loud: concatenation targets with `ArraySel` leaves, signal
indices below the first dimension of a chain, and arrays declared through a
typedef (no recoverable dimension list).

Review fix (same day): a parameter/genvar-CONSTANT select (`i[0]`, `P[3:1]`)
now has a self-determined width (`selfWidth2`: one bit, or the part's
width), so it is exact in self-determined positions — `{i[0]}`,
`{8{i[0]}}` — where it previously materialized as a 32-bit literal and the
consuming gate read x (pre-existing, newly reachable through `ArraySel`
targets; rows `gvcat`, `gvcat_n6`). An unexpected extractor failure on a
select chain past two dimensions is now `Unsupported`
(`…:array-select`) rather than the legacy nested fallback.

## `always_comb` in the comb settle theorem — 2026-10-27

The Design2 combinational settle theorem now covers designs whose logic sits
in `always_comb` blocks. `LeanModels/Sv/Comb2Proc.lean` runs a body
SYMBOLICALLY (`Stmt2.symExec`) — blocking assignments to whole signals,
constant slices and constant-literal element selects under `begin … end`,
`if`/`else`, `case` and `case … inside` with or without `default` — and
produces one equation per written window over the body's pre-state: a read
of a written window is replaced by its equation, branches join under a known
bit (`(|c) === 1'b1`, exactly the interpreter's `if` truthiness, or the arm's
hit), a window a path does not write keeps its pre-state value, and a bit
write inside a written window splices into it (the "default, then override"
idiom). `Design2.lowerComb` replaces every body by the continuous assign
`{w₀, …, wₖ} = {E₀, …, Eₖ}`. On states with the comb shape a successful body
run, at any fuel, IS that assign's write, and the body completes at every fuel
from the static bound `Stmt2.fuelB` (`symExec_sound` / `symExec_total`, one
fuel induction over `execStmt2`/`execCase2`/`execStmts2`); a step simulation
(`CombSim`) lifts that to `Runs2.lowerComb_iff` — a design and its lowering
have the same completed runs under every schedule whenever the lowering is in
the comb profile. The settle theorems of `Comb2Sound`/`Comb2Term` therefore
apply unchanged (`Comb2*.lean` are untouched): `Terminates2.of_lowerComb_acyclic`,
`Models2.of_combProc` (with `_inputs` / `_pointwise`), the fixpoint
characterization `procFixpoint_iff_combEqs` (every process, the bodies
included, maps the state to itself iff the lowered equations hold), and the
per-window read-back `CombEqs.symWindow` / `_ident`. The lowering refuses a
body whose equations read a window the body itself writes
(`SymState.selfReadFree`): latches, and every read of a window's pre-state
value by a body that writes it (see the review fix below). For one-process
designs `CombDesign.of_single` reduces the profile to `decide` checks on
closed data, and `Acyclic.of_lowerComb_single` gives the certificate with no
proof at all.

`LeanModels/Sv/Comb2ProcExample.lean` proves, under `⊨₂` with `Terminates2`:
a full adder written as one `always_comb` with a temporary and an `if`/`else`
(`fa_correct`, the gate-level adder's statement), a default-then-`case`
4-way multiplexer (`mux_correct`: `y = d[sel]`), and a default-then-override
one-hot decoder (`dec_correct`: `y = en ? 1 << sel : 0`), each with `run2`
`#guard`s, and an `N`-bit adder/subtractor with a zero flag
(`if (sub) y = a - b; else y = a + b; z = ~|y;`) for EVERY `N`
(`as_correct`, `as_terminates`; the symbolic execution and the profile are
evaluated by `simp` with `N` a variable). Differential rows `fa_comb_proc`,
`mux4_case`, `onehot_dec`, `latch_comb` and `addsub_comb` (`N` = 4, 1, 8),
with `x`/`z` conditions and `case` subjects, match Icarus, and each
fixture's `agree.lean` checks that the SV source instantiates to exactly the
proved design (`addsub_comb` at `N` = 1, 2, 4, 8, 32). Refused by the lowering: nonblocking assignments,
dynamic-index and concatenation targets in procedural code, a whole read of
a partly written signal, reads or writes that straddle a written window,
branches that write different overlapping windows of one signal, and designs
with clocked processes, and (self-read check) latches and every body that
reads a window it writes before or without writing it; the extractor refuses
procedural `for`. Open: a packaged tactic for evaluating the symbolic
execution at symbolic widths (today a `simp` call over the definitions), a
window-level termination rank (`Acyclic` ranks processes, and a body lowers
to ONE assign, so a body that writes `t` and reads `w` next to
`assign w = t + 1` is rejected as a cycle although no window depends on
itself; Icarus and the settle semantics both settle it — split the body into
separate blocks), and `always_ff` (the settle theory is comb-only).

Review fix (same day): self-reads. The first version accepted a body that
reads a window it writes only later (`always_comb begin y = t; t = a; end`)
and proved, through `Models2.of_combProc`, that `y = a` on every snapshot.
That is what the settle semantics computes (`run2` re-runs a comb process
until nothing changes) and what Yosys 0.53 `proc` synthesizes
(`assign y = a`), but not what an event-driven simulator does: IEEE
1800-2023 §9.2.2.2.1 leaves the variables a block writes out of its
implicit sensitivity list, and a block is never woken by its own writes, so
Icarus 12 runs the block once per change of `a` and shows `y` one change
behind (`a` = 01, 10, 11 gives `y` = 00, 01, 10). A narrower fix that
exempted the pre-state values a join keeps (`Win.held`) would still accept
`if (c) t = a; y = t; t = b;`, where the settle answer is `y = c ? a : b`
(Yosys agrees) and Icarus shows the previous `b` while `c` is low. The
lowering now refuses every body whose lowered equations read any window of
its own write set (`SymState.selfReadFree`, latches included), and
`runCombProcess2_alwaysComb_idem` proves the property that makes the two
readings agree on what remains: one run of an accepted body is already the
body's own fixpoint. Fixtures `Examples/system-verilog/sem2/rbw_comb` and
`rbw_held` pin the refusal on the instantiated SV (`rbw_refused`,
`held_refused`) and the `run2` traces. They have no `cases2.json` rows:
the disagreement is the MODEL's, since IEEE sides with Icarus, and an
`oracle_disagreement` declaration records only a simulator's departure from
the standard. Outside this API, `run2` still runs a self-reading
`always_comb` with the settle answer. That divergence from the standard's
event semantics (on which Sem2 agrees with Yosys, not Icarus) is open;
remodelling `combSettle2`, refusing such bodies at ingestion, or a
semantic row in `docs/sv-declared-divergences.json` are the options.
(Decided 2026-10-28: Sem2 is kept and the divergence is the semantic row
`sv-div-3`; see the entry of that date.)

## Indexed part-selects: lsb-overhang targets and run-time bases — 2026-10-27

Indexed part-selects `x[b +: w]` / `x[b -: w]` and range selects `x[hi:lo]`
whose base and bounds are elaboration-time constants over parameters and
genvars (`rev_up[i*W +: W] = a[(N-1-i)*W +: W]`, `a[N*W-1 -: N]`) already
lower through `ArraySel` (entry above); this entry closes the two gaps that
remained, both in `LeanModels/Sv/Param2.lean`, `Sem2` unchanged. (1) A
TARGET overhanging the LSB end of its dimension (`w[N-3 -: 4] = b` at
`N < 6`), previously loud, now writes exactly its in-range bits, which take
the RHS's upper bits (IEEE 1800-2023 §11.5.1): `arrayPartTarget` lowers it to
a concatenation target whose low leaf is a zero-effect sink window just
past the vector's msb (`LVec.insertAt` drops every bit there). It runs in
continuous assigns and blocking statements; a nonblocking write to it stays
loud (`resolveLhs2`), and it is outside the comb settle profile (the
`always_comb` lowering refuses procedural concatenation targets). (2) A
RUN-TIME base in a READ (`v[sel +: 4]`, `a[sel*W +: W]`), previously
`RangeSelectExpression:dynamic-indexed`, is admitted on a 1-D vector with a
descending range: the extractor emits `ArraySel` with the base as a value
expression (`_sym_dynamic_part_select`), and `dynPartPlan`/`dynPartRead`
lower it to a right shift of the vector padded with x above and below, under
a guard, so every out-of-range bit reads x and an x/z base reads all x. A
signed base is `RangeSelectExpression:dynamic-signed-base`; a run-time base
on a procedural target is `AssignmentExpression:target` (continuous ones are
illegal SV); after an element select, over a multi-dimensional array or an
ascending range it keeps `dynamic-indexed`, and in Lean it is
`ArraySel:dynamic`.

Proof handles (`LeanModels/Sv/Gen2.lean`): over a 1-D zero-based descending
vector with symbolic base and width, `arrayPartGeom_up_desc0`/`_down_desc0`
compute the geometry, `arrayPartTarget_up_desc0`/`_down_desc0` and
`arrayPartRead_up_desc0`/`_down_desc0` give the in-range `slice`, and
`fitExpr2_arrayPart_up_desc0`/`_down_desc0` read it in a same-width context
with no resize. `instExpr2_arrayPart` now carries the hypothesis
`dynPartPlan … = none` (discharged by `dynPartPlan_of_evalInt` or
`dynPartPlan_of_geom`; `mul2d/gen.lean` changed one `rw`), and
`instExpr2_arrayPart_dyn` is the run-time case. `sv2_inst_simp` unfolds
`dynPartPlan`. `Examples/system-verilog/partsel/gen.lean` proves, for every
`N` and every `W ≥ 1`, that the lane-reversal generate block of
`partsel.sv` (one `+:` and one `-:` template, targets and reads)
instantiates to the `W`-bit window copies `rev[i*W +: W] ← a[(N-1-i)*W +: W]`
(`partsel_rev_expand`; `partsel_rev_instantiated` at the environment
`instantiate2` builds), axioms `[propext, Classical.choice, Quot.sound]`, and
pins the lowered nodes of the overhanging and run-time selects at the row
parameter points.

Differential rows (Icarus 12.0): `partsel` (`N`, `W` = 4, 3), `partsel_n2_w5`,
`partsel_n6_w2`, `partsel_n5_w1`, `partsel_n1_w4` — reads overhanging
either end, a range select above the msb, procedural writes overhanging
either end or fully out of range, run-time bases over every value and with
x/z bits — all match, as does `array_oob_lsbwrite_l1`.
*(Xcelium audit round 6, lane A, 2026-10-29 correction: "all match" was a
statement about Icarus 12.0 alone, and Xcelium 24.03-s004 does not agree on
the PARTLY out-of-range selects: it reads them all x and drops an
overhanging write. The five `partsel*` rows are loud-refusal rows since
round 6 (`ArraySel:partial-overhang`); the run-time-base reads and the
wholly-outside selects are not what is refused. See "Xcelium audit, round 6,
lane A" below.)*
`array_oob_lsbwrite` is a declared disagreement: an lsb-overhang write into
an INNER dimension (`w[1][-1 +: 2]`) is linearized into `w[0][3]` by Icarus
and Yosys (`docs/sv-oracle-disagreements.md`, "Linearized packed-array
indices"). Measured: Icarus cannot be the oracle for a CONTINUOUS assign
that overhangs either end — `vvp` aborts (`adr+that.size_ <= size_`,
`vvp_net.cc:1180`) on the msb side, and elaboration stops with `sorry: part
selects straddling the start of signal` on the lsb side — so the overhanging
writes in `partsel.sv` are procedural. Yosys 0.53 `prep; eval` gives
`partsel`'s values at `(4, 3)`.

Out of tier, loud: signed and 2-state declarations (`PortSymbol:signed`,
`PortSymbol:2state` — the gap is the declaration, not the select);
part-selects of a PARAMETER (`P[i*4 +: 4]`, a constant table) stay
`RangeSelectExpression:dynamic-indexed`; run-time bases on targets and
below an element select.

## Width-exact constant labels and 32-bit run-time bases — 2026-10-28

An independent review of the entry above found four silent disagreements
with Icarus 12.0 and Yosys 0.53, all now fixed or refused. (1) The constant
tier (`evalInt`, `LeanModels/Sv/Param.lean`) evaluated select labels and
generate conditions over unbounded integers, so `v[K + 3'd4 +: 2]` with
`parameter logic [2:0] K = 5` selected bit 9 where every simulator selects
bit 1 (3-bit arithmetic wraps, IEEE 1800-2023 §11.6/§11.8); the same root
cause hit element, range and bit selects and a generate-if. `evalInt` now
keeps its mathematical fast path for the INT class only — unsized
integers, genvars, system calls and `int`/untyped parameters, the
`PExpr.isInt` test — and sends every node with any other operand to
`evalSized`, the §11.6/§11.8 rules verbatim (`ctype` self-determined types,
`evalAt` at the propagated type, `canonInt` wrapping; x reads, division by
zero and out-of-range constant selects loud). Typed parameters that are
not `int` bind in the new `IEnv.nvals` with their width and signedness
(`bindParams`, `bindLocal`), so a `ParamRef` is INT exactly when it is bound
in `vals` and proofs holding `env.vals.lookup n = some v` need nothing more.
(2)/(4) The signedness of a 32-bit typed parameter was not in the envelope
(`int` and `int unsigned` looked alike), so `v[UI - 1 +: 4]` at `UI = 0`
read `v[2:-1]`. The extractor now emits `signed` on `ParameterDecl` and
`LocalParam` where the type departs from the default (signed iff 32 bits
wide), and `signed: true` on signed literals in symbolic constant positions
(`docs/sv-envelope-schema.md`, "Constant typing"); only
`sem2/fifo/cv32e40p_fifo.sv.json` changes among the reproducible
envelopes. A label that wraps past `2^31` (`UI - 1`, `U - 1` at 0) is where
the tools split — Icarus reads it as a huge unsigned index, Yosys as a
negative one — so it is refused (`partOffsetsWild`, `ArraySel:index-range`;
legacy `[msb:lsb]` reads `PartSel:bounds`). (3) A run-time part-select base
was read unsigned at its own width; both tools read a 32-bit base as a
two's-complement `int` (`v[s - 2 +: 4]` at `s = 0` is `v[1:-2]`), so a
32-bit base now lowers through `dynPartRead32` (sign-extended to 34 bits
plus `w - 1`, one unsigned guard for both ends), a narrower one keeps
`dynPartRead`, and a wider one is loud (Icarus truncates it to 32 bits,
Yosys does not) — `dynBaseRead` in Lean, `RangeSelectExpression:dynamic-wide-base`
in the extractor. Minor: a concatenation-target leaf whose
lowered window is not its declared width (a part select overhanging its
vector at that parameter point) is refused (`concatLeafExact`) instead of
shifting the RHS split; a `localparam` inside a generate block is a loud
`GenerateDecl:LocalParam` item instead of an `Ingest2` parse failure.

Recorded restrictions: INT-class arithmetic is still unbounded (a 32-bit
`int` overflow is not wrapped); an UNTYPED parameter with a sized default
(`parameter P = 3'd5`) is read as an `int` (its override value's type),
while slang elaborated the envelope at the default's 3-bit type. (Both
superseded by the next entry: the default point is modelled, value reads
at overridden points are loud, and overflow is caught by `int32Agrees`.)

Proof surface: the compositional `evalInt_*_of` lemmas (`Gen2.lean`),
`evalInt_slt`, `genvarSeq_ascending(_length)` and the
`GenItem.expand2_genFor_ascending*` family take INT-class side conditions
(`isInt_paramRef_of`, `isInt_binary_of`, `rfl` for genvars and integers);
the legacy part-select lemmas (`instExpr2_partSel_ident`, `instLhs2_partSel`,
`fitExpr2_partSel_ident*`) take `msb.isInt env = true ∨ m < 2 ^ 31`;
`instExpr2_arrayPart_dyn` now ends in `dynBaseRead` (`dynBaseRead_lt32`,
`dynBaseRead_32`). `ripple_add`, `mul2d` and `partsel` were updated
accordingly, statements of their headline theorems unchanged.

Differential rows (Icarus 12.0): `const_wrap` and `const_wrap_k*_u*` sweep
`K`, `U` and `UI` over `sem2/const_wrap/const_wrap.sv` — sized-label wraps on
`+:`/`-:` reads and an always_comb target, a bit select, an element select
and a range select on `[19:4]`, a canonical range select, a widened label,
`U - 4'd1`, an `int unsigned` label and a generate-if; `dyn32`
(`sem2/dyn32/dyn32.sv`) drives `v[s - 2 ±: 4]`, a concatenated 32-bit base
and a raw 32-bit input base through negative, huge and x/z values. All match.

## Parameter types and context widths across parameter points — 2026-10-28

A second independent review found three more places where slang's
DEFAULT-point elaboration leaked into other parameter points as silent
disagreements with Icarus 12.0 and Yosys 0.53; all are now exact or loud
(`docs/sv-envelope-schema.md`, "Parameter types and context widths across
parameter points"). (1) A parameter with a range and no type
(`parameter [3:0] V4 = 4'd9`) arrived as `type: null` and was read as an
unbounded `int`, so `v[V4 + 4'd8 +: 2]` selected bit 17 where every
simulator wraps to 1 (IEEE 1800-2023 §6.20.2 makes it 4-bit unsigned
whatever the override; an override of 25 reads 9). The extractor now
types implicit ranged parameters (`_sym_implicit_ranged`,
`_sym_param_syntax_dims`) and gives dimensioned keyword types
(`logic signed [3:0]`, `bit [4:0]`) their symbolic dimensions instead of
`packed: null`; a rangeless `parameter signed P` records `signed`. (2) An
untyped parameter with a sized default (`parameter P = 3'd5`) was read as
an `int` even where it is not overridden; there its type is the default's
and `P + 3'd4` wraps. `PDesign.atPoint` (`Param.lean`) resolves a
partially overridden point and retypes every not-overridden untyped
parameter whose default is not `int`-typed; `crossCheck` and the
differential runner instantiate through it. Where such a parameter IS
overridden its value-tier tree is still the default point's, so a value
read of it is loud there (`PParam.overrideRetypes`, set at ingestion by
`markOverrideRetypes`; `IEnv.stale`; `ParamRef:override-type`, untyped
localparams defined from it included), while its constant uses are exact.
(3) Context-determined widths came from the default-point tree: `-a`/`~a`
with `logic [N-1:0] a` computed at N bits and zero-extended (at N = 2, `-a`
for `a = 10` gave `0010`, not `1110`), and `+`/`-` truncated an operand
wider than the context first, dropping the x of an out-of-range bit
(`v[1 +: N] + 4'd9` at N = 8 is `xxxx`). `instExpr2` (`Param2.lean`) now
extends `- ~ +` operands to the context, runs `+ - *` at the widest
x-carrying operand (`rigidMax2`, `ctxOpWidth2`) and truncates, truncates
`/ % ** << >>` results to the context (`ctxTrunc2`), reads an implicit
conversion's operand width in `selfWidth2` (never its default-elaborated
`width`), and refuses a `$signed` operand that must be widened
(`Resize:signed`). The extractor emits `Resize(width, Literal)` for a
sized literal its value context widens (`_sym_literal_widening`), which
fixes self-determined widths such as `{a + 1'b1, 1'b0}` at N = 1; that
changes `sem2/fifo` and `sem2/register_file_ff` among the reproducible
envelopes (regenerated). Minor: a signed constant label operand
sign-extended to 32 bits (`SB + 5`, `S4 * -1`) is a `SignedResize`
(`_sym_signed_widening`) and evaluates; a constant select whose label still
fails to convert keeps its own refusal kind
(`_sym_constant_label_refusal`) instead of the misleading
`…:dynamic-signed-base`.

32-bit `int` overflow: the proof-facing constant tier keeps INT-class
arithmetic unbounded (bounding it would put `N < 2^31`-style hypotheses
into every ∀-N theorem). `PDesign.int32Agrees` compares a point's
`instantiate2` design with one built under exact 32-bit `int` arithmetic
(`IEnv.int32`: INT parameters and `int` localparams bound at `(32, signed)`
and evaluated by `evalSized`); the differential runner and `load_design_sv2`
(at the defaults) refuse a point where they differ, e.g.
`v[(N*N) >> 30 +: 4]` at `N = 65536`. A checker instantiating a family at
concrete parameters should call it too.

Kept loud and recorded (schema): run-time bases over a range with a
negative lsb, a parameter's `$bits` in a label, a literal-base select
partly out of range, concatenation targets with part-select leaves,
concatenation labels, and implicitly typed nets/net ports (`wire [7:0]`;
a partially driven net's undriven bits are z, which the semantic tier
does not model — an implicit-net admission tried this round was reverted
when it turned the refusal into x-vs-z mismatches).

Proof surface: `instExpr2_add`/`instExpr2_sub` take
`(ctxOpWidth2 env elems l r).getD w ≤ w`, `fitExpr2_of_rigid_ne` takes
`e.signedCast = false`; `PDesign.instantiate2` is
`instantiate2From {}` (`instantiate2_eq` unfolds both). Headline statements
of `ripple_add`, `mul2d` and `partsel` are unchanged.

Differential rows (Icarus 12.0): `param_types` and seven override points
(`sem2/param_types`: untyped, ranged, signed-ranged, 32-bit-unsigned,
`logic signed`, `bit`, `byte` parameters in `+:`/`-:` labels and a value
comparison); `ctx_width` at N = 4, 1, 2, 3, 6, 8 and `ctx_width_n2` at
N = 2, 4, 8 (the same body elaborated at a narrower default, so the tree
carries the conversions of N = 2). Lean guards in `Param2.lean` pin the
`-a`/overhang values, the stale-read refusal and `int32Agrees`.

## Module instances in sv-0.2 symbolic mode (hierarchical designs) — 2026-10-28

sv-0.2 symbolic mode now admits module hierarchies. The extractor emits a
module instance — at module level or inside a `generate` for/if body — as ONE
`Instance` node (definition name, lexical generate path, symbolic parameter
overrides, one `PortConn` per child port) and appends the definition of every
module the top instantiates, transitively, to `design.modules`, each
elaborated ALONE at its own defaults (a separate slang compilation per
definition, so its `resolved` metadata is its own and the load gate
cross-checks it like a top). Designs without instances are byte-identical:
all 101 reproducible sv-0.2 envelopes re-extract unchanged
(`docs/sv-envelope-schema.md`, "Module instances").

The Lean side FLATTENS at instantiation time
(`LeanModels/Sv/Hier2.lean`, `PDesign.instantiateH`): at each instance, at the
current parameter and genvar values, the overrides are evaluated in the
instantiating scope, the child is brought to that parameter point
(`PDesign.atPoint`) and instantiated recursively, its declarations are hoisted
under `<path>.<inst>.<signal>` (`g_bit[3].fa.s`, port flags cleared), its
processes renamed, and every port connection becomes a continuous assignment
(§23.3.3) with LRM width coercion. `Sem2` is unchanged; `GenItem` gains the
`inst` constructor, which the flat instantiations keep as a loud process.
`load_design_sv2` defines `name.plib` and routes `name.sem` through
`PDesign.instantiateHD2` for a hierarchical envelope (single-module
envelopes elaborate exactly as before); the differential runner dispatches
the same way and re-checks `Design2.namesNodup`. Measured and recorded: an
input actual narrower than its port is admitted only where the LRM reading
(slang, Verilator 5.042) and the Icarus 12.0 / Yosys 0.53 reading
(self-determined, zero-padded) agree — any other is loud
(`PortConn:context-width`, `docs/sv-oracle-disagreements.md`) — except that
unbased-unsized fills are admitted anywhere among the agreeing operands and
take the LRM reading, which Verilator and Yosys share and Icarus alone does
not (declared row `hier_fill_ctx`); unconnected input nets read z, `var`
inputs x (Icarus agrees); a child flop whose clock is a child input port
bare-connected to an input port of the instantiating module flattens to a
flop on that signal (so every flattened flop is clocked, through bare
connections, by an input port of the top), any other clock is loud.

Proof surface (`LeanModels/Sv/Hier2Gen.lean`): the walk's equations
(`expandListH_cons_ok`, `GenItem.expandH_inst`, `GenItem.expandH_genFor_of`,
`expandItersH_eq_flatMap`, `GenItem.expandH_genFor_ascending_flatMap`), the
instance step `instExpandH_of`, the decomposition
`PDesign.instantiateRec_of_ok` (the `instantiate2_of_ok` twin) and the
conservative extension `PDesign.instantiateH_flat` /
`PDesign.instantiateHD2_flat` (an instance-free design flattens to exactly
`instantiate2`). `Examples/system-verilog/ripple_fa/gen.lean` proves, for
every `N`, the whole flattened process list of the ripple-carry adder written
with a `full_adder` per bit in a generate loop (`ripple_fa_processes`, the
`ripple_processes` twin) and its declarations (`ripple_fa_decls`).

Differential rows (Icarus 12.0, all PASS): `ripple_fa_n4_cin0/1`
(exhaustive at N = 4), `ripple_fa_n4_xz`, `ripple_fa_n1/n3/n8`;
`hier_params*` (named/ordered overrides and connections, expressions on
inputs, an output into a part select, three instances of one definition at
three parameter points; N = 3, 2, 5); `hier_width*` (narrow/wide coercion in
both directions; N = 4, 2, 6); `hier_nested*` (three levels, instances in
generate for/if, `.*`, unconnected net/var inputs and output; N = 3, 2, 4);
`hier_clk*` (clocked children, `.clk` implicit connection; W = 4, 1, 6);
`hier_fill` (bare and masked fills in narrower input actuals). Yosys 0.53
agrees on spot checks of `hier_width` and `hier_params` and on all 32
two-state points of `hier_fill`. Declared Icarus disagreement:
`hier_fill_ctx` (`iverilog-port-fill-self-determined` — ten nested-fill
shapes; Yosys agrees with the model on every two-state point, Verilator on
every two-state output).

Recorded refusals: `inout`/`ref` and interface ports, interface instances,
instance arrays, port default values, type-parameter overrides, `defparam`,
`bind`, recursive instantiation, escaped identifiers containing `.[]` on an
instance path, a typed child parameter overridden by a parameter expression
needing a narrowing conversion (`ConversionExpression:width`; literal
overrides are admitted), a child definition with a parameter that has no
default (`ModuleDefinition:elaboration`: slang cannot elaborate it alone, so
it is not in the library), and an instance inside a generate branch not
taken at the default parameters (slang leaves it unbound as
`UninstantiatedDefSymbol`: loud wherever that branch is taken) — for a
branch inside a generate-for, not taken at the loop's FIRST iteration, since
the extractor binds the body from that iteration.

Single-clock gap, recorded (2026-10-28): the cycle semantics runs every edge
process on its one clock whatever the clock name, so a TOP-level
`always_ff @(posedge g)` on a derived or gated `g` (`assign g = clk & en`) is
admitted and fires while `en = 0`, where every simulator holds it. This is
inherited from the flat tier, not introduced by flattening: a child flop is
admitted only on a clock that traces, through bare input-port connections,
to an input port of the top (`clockGuardProc`, `Hier2.lean`; `#guard`s for
the gated, child-internal and two-level cases), so no flattened child flop
runs on a derived clock. Closing the top-level half needs a clock-domain
check on `Design2` (or a multi-clock cycle semantics) and is not started.
CLOSED at the loader on 2026-10-30 (WP-Q0): see "The clock-discipline guard"
at the end of this charter. `name.sem` still instantiates such a design
(the recorded lemmas are stated for the unguarded family); `load_design_sv2`,
the differential runner and `probeCheckString` refuse it.

One driver per bit after flattening (2026-10-28, verifier round 2):
flattening adds the port-connection assigns AFTER the extractor's
overlapping-driver guard has run on each module alone, and `Sem2` gives
several continuous drivers of one bit issue order (last write wins), so two
instance outputs on one wire (verifier `w_multi1`: Icarus resolves the
net), a parent `assign` and an instance output on one bit (`w_multi2`;
`w_inval`, illegal for a variable) were silently ordered. Now every module
of the hierarchy, at the instance's own parameter point, must drive each bit
of its OWN signals once (`driversOk`, `Hier2.lean`): the windows of its
continuous assignments — its `assign`s and its instances' output connections
alike — pairwise disjoint, none on a signal a procedural process writes or
on an input port, and no procedural write to an input port; otherwise a loud
`PortConn:driver` process is appended, so `run2`, the differential runner and
`load_design_sv2` refuse (`#guard`s in `Hier2.lean`; the three repros now
refuse). Every child is checked, instance-free ones included; an
instance-free TOP is the flat tier's, unchanged (`instantiateH_flat`
re-proved). The `ripple_fa` acceptance proves the rule for every `N`
(`ripple_fa_driversOk`, through `driversOk_of_continuous`, `Hier2Gen.lean`),
so its headline statements are unchanged.

Integer actuals (same round): slang binds an input actual converted to the
port type of the instance it bound (defaults / first generate iteration), and
an integer constant under that conversion was folded to a literal of THAT
width (`.i(5)` into `W = g` ports: `001011` where Icarus has `101011`;
`.i(-1)`, `.i(37)`, `.i(N*3-1)`). The extractor (`_sym_port_actual`, additive)
emits the unconverted INT-class tree, which Lean fits per point exactly; a
genvar actual narrower than its port (formerly `ConversionExpression:width`)
is admitted the same way; an integer constant into a port wider than 32 bits
is loud (`PortConnection:int-width`). Rows `hier_intact*` (N = 4, 2, 7, 8,
30) PASS against Icarus 12.0, and the verifier's `w_lit`, `w_gvw` and
`w_stale` repros re-extracted now match it. Existing envelopes re-extract
byte-identically.

Flat-tier gaps recorded by the same verifier round, NOT fixed (both predate
F3 and change many envelopes if fixed, so they wait for an extractor pass
coordinated with upstream): (1) an unsized integer constant assigned to a
parameter- or genvar-width target in a flat module (`assign o1 = -1` with
`logic [N+1:0] o1`; `assign neg[(g*(g-1))/2 +: g] = -1` in a genvar loop) is
folded at the default width by `_sym_conversion` — `w_stale_flat_n7` gives
`000111111` where Icarus has `111111111`, `w_gvw_flat` `001011` against
`111111`; the fix is `_sym_port_actual`'s peel at that conversion. (2) The
extractor's symbolic overlap guard sees only `Int`-index windows
(`_symbolic_target_windows`), so overlapping continuous drivers whose
windows depend on a genvar or parameter in an instance-free top are not
refused; the hierarchical rule above covers every child and every top with
an instance, not that flat case. Also documented, not rows: a CONNECTED
`input var` port (Icarus coerces it to inout and reads the parent's input as
x; Verilator and the model agree) and a z/z bit under an x/z `?:` condition
(Icarus z, Table 11-20 x) — `docs/sv-oracle-disagreements.md`.

## Registered and documented simulator/synthesis splits; Icarus host framing — 2026-10-28

A documentation-and-harness pass (no Lean, extractor or `Sem2` change) that
makes the known places where `run2`, Icarus 12.0, Yosys 0.53 and the LRM
part ways machine-tracked or written down, so an svGolf proof about a design
cannot rest on one of them without a record saying so.

**Self-reading `always_comb` is a declared SEMANTIC divergence, `sv-div-3`**
(`docs/sv-declared-divergences.json`, the tier's first semantic row). Lead
decision: `Sem2` is kept. On `if (c) t = a; y = t; t = b;` (`sem2/rbw_held`)
and `y = t; t = a;` (`sem2/rbw_comb`) `run2` settles to the fixpoint, which
is what Yosys `proc` synthesizes and what svGolf scores; IEEE 1800-2023
§9.2.2.2.1 and Icarus run the block once per wake-up and show the stale `t`.
The row's two guards live in `harness/sv_divergence_probe.py` in the
layered shape of family-architecture §5.0a (b): the MODEL side is the
build's own `#guard (run2 heldDesign …)`/`rbwDesign` pins in
`LeanModels/Sv/Comb2ProcExample.lean`, tied to the committed SV by the
fixtures' `agree.lean` (the probe checks they exist outside comments and
reads their stimulus and traces, and runs no Lean); the ORACLE side is RUN —
Icarus on the committed SV with the pin's own stimulus (`run2` `01 10 11` vs
Icarus `01 01 11`; `00 01 10 11` vs `00 00 01 10`). `sv_div_3_has_not_widened`
also requires Yosys `prep; eval` to give the settle answer on all 32 and 4
two-state input points (the reason the debt is carried), Icarus to give
exactly the declared stale trace (it differs from `run2` only where `t` is
read stale, and agrees on the `c = 1` cycle that writes `t` first), and the
settle-theorem refusals (`rbw_refused`, `held_refused`, `lowerComb.isNone`)
to stay declared. The failure direction was run against mutated copies:
a `run2` pin changed to Icarus's trace (a remodel), a commented-out pin, a
removed refusal, a removed `agree.lean` link and a de-self-read SV body each
turn a guard red; without `iverilog`/`yosys` on PATH the guards report
COULD NOT VERIFY and fail closed (the shared register therefore now needs
both tools on the host that runs it). The 2026-10-27 entry's open question
is answered there.

**`sv-div-1`'s fixture guard is repaired.** `sv_div_1_still_divergent`
looked for a recorded Xcelium fixture by FILE NAME, and the CI readiness
probe `harness/sv/xcelium_probe.py` and its unit test (34849ef6,
2026-10-09) match that test while recording no operator result: the guard
reported the row fixed and `harness/divergence_register.py` exited 1 from
that commit on. Instrument source files (`*.py`, `*.pyc`, `*.sh`) are no
longer counted; a recorded result file named for Xcelium still retires the
row. No Xcelium fixture exists, so the row is still divergent. Recorded in
the row (`guard_repaired`).

**Synthesis-side divergences are written down**
(`docs/sv-oracle-disagreements.md`, "Synthesis-side divergences"). On two
`always_comb` shapes the proof API accepts, the model, Icarus and the LRM
agree and Yosys does not: a `unique`/`priority case` with no matching item
(the block's earlier value; Yosys reads `full_case`, `prep; eval` gives x
and the netlist `y = a`), and x/z bits in a plain `case` item (`2'bx1`
never matches `01`; Yosys's `$eq` makes it x under `eval` and a wildcard in
the netlist). The svGolf post-synthesis check must flag designs that rely
on either. `unique0` and a `unique case` with a `default` agree everywhere.

**Two declared Icarus disagreements, hash-bound like the others.**
`array_param_labels_l7` (`iverilog-single-element-minus-select`): Icarus
evaluates `x[b -: w]` over a single-element range `[k:k]` with a constant
(elaboration-time) base as `x[b +: w]`, in reads and writes, where the
model, slang and Yosys select labels `b` down to `b-w+1`; with a run-time
base Icarus reads labels `b` down to `b-w+1` as well and all three agree
(verifier probe `vp_onedyn`). At `L = 7` the fixture's constant-base
`u[L+1 -: 2]` reads `x1` in the model and
`xx` in Icarus ("Single-element range direction"). `concat_undriven`
(`iverilog-concat-target-undriven-init`, new fixture
`Examples/system-verilog/sem2/concat_undriven/`, envelope regenerated by the
extractor): `assign {y[3:2], z} = x;` leaves `y[1:0]` undriven, z in Icarus
and x in the model ("Partial variable initialization"). Out-of-range
concatenation leaves (`{y[4:3], z, y[2:0]} = x` over `[3:0]`) cannot be
compiled by Icarus; Yosys `prep; eval` agrees with `run2` on all 64
two-state inputs — a note, not a row.

**Refusals documented** (`docs/sv-envelope-schema.md`, "Recorded refusals:
parameter roots, first-dimension labels, concatenation targets"): an indexed
part-select whose root is a parameter or localparam (`MASK[i*2 +: 2]`,
`RangeSelectExpression:dynamic-indexed` although the base is constant), and
a range select on such a root that is partly out of range at the
instance's parameters (`MASK[P+1:P]` over `[7:0]` at `P = 7`, refused by
`run2` as `PartSel:base` where Icarus and Yosys read the missing bit as x;
in range it is admitted and matches Icarus, and on a signal root the
partly-out-of-range select is admitted and agrees with both); a
negative constant label on a canonical first dimension (legacy `BitSel`:
`BitSel:index` on a read, `AssignL` on a write, while labels above the msb
and every `ArraySel` select read x / write nothing); and the concatenation
targets still refused — genvar/parameter-indexed leaves, `+:`/`-:` leaves, a
right-hand side reading a target signal's name even on disjoint bits, a
signed right-hand side that needs extension, `ArraySel` and `wire`-vector
leaves.

**Icarus host framing.** The sixteen `icarus_unavailable` crash signatures
were recorded with Ubuntu's Icarus 12.0-2build2 and ERRORed on every run
with Homebrew Icarus 12.0 on macOS, which reports the same assertion
through macOS libc and the aborted `ivl` stage through a bash job report
with run-varying process ids and temporary names.
`harness/sv/oracle_disagreements.py` now reduces exactly those two framings
to one canonical text on both sides before comparing (file, line, function
and expression of an assertion are kept; which pipeline stage died of which
signal is kept); stage, exit status, stdout and every other line stay exact.
`HostFramingTests` (`harness/sv/test_oracle_disagreements.py`) accepts every
recorded crash in its macOS framing and the two measured macOS signatures,
and rejects twelve mutations (another assertion, line, function, expression
or file; an aborted preprocessor; a segmentation fault; a bare `Aborted`; a
missing abort report; another exit status or stage; an extra line).

**Found, NOT fixed here (open, model-side, silent).** A `case` item wider
than the case subject is truncated to the subject's width: with
`logic [1:0] s`, `case (s) 4: y = 1;` matches `s = 00`, `3'd5:` matches
`s = 01`, `3'b100:` matches `s = 00` and `-1:` matches `s = 11` in `run2`,
while Icarus 12.0, Yosys 0.53 (`prep; eval` and the synthesized netlist)
and IEEE 1800-2023 §12.5.1 (subject and items evaluated at the widest of
them) give the `default`. The always_comb lowering accepts the shape
(`lowerComb` is `some` on the `case (s) 4:` probe, as on the `unique case`
and x/z-item probes above), so it reaches the settle-theorem API as well as
`name.sem`. The envelope is right — slang wraps the subject in `Resize`
to the widest width and emits the items at it — and
`LeanModels/Sv/Param2.lean` drops it: `instStmt2`'s `caseStmt` arm fits
every item to `sctx := selfWidth2 env elems subj`, and since this date's
"Parameter types and context widths" entry `selfWidth2` reads a `Resize`
as its OPERAND's width. Verifier probe `ac_casew` (2026-10-27, before that
change) still gave the IEEE answer. A fix computes `sctx` as the maximum of
the subject's and every item's self-determined width. Not a row: it is
neither a simulator's departure from the standard nor a decision the tier
has taken, and a failing row would only hide it inside the suite's FAIL
count. The independent verifier reproduced it on `vr_cwide` (2-bit `s`;
`case (s) 3'd6: y = 1; default: y = 5;` and `case (s) 2'd1: q = 2; -2:
q = 3; default: q = 4;`): at `s = 10` `run2` gives `y = 001 q = 011`,
Icarus and Yosys `prep; eval` give `y = 101 q = 100`, every other cycle
agrees. Routed to the owner of `Param2.lean`; once fixed, a `cases2.json`
row with an item wider than its subject (`vr_cwide`) pins it.

**Open for the lead: the fleet floor now needs EDA tools.**
`harness/divergence_register.py` is in `tools/triad.sh`'s `DEFAULT_FLOOR`
(every lane's floor) and in `tools/c_torture_gate.sh`, and `sv-div-3`'s
guards fail closed without `iverilog`/`vvp` and `yosys` on PATH (measured
with `PATH=/usr/bin:/bin`: COULD NOT VERIFY on both guards, exit 1). CI
installs Icarus but not Yosys. Either the floor's rationale in
`tools/triad.sh` records that requirement, or every host that runs the
floor installs Yosys; this pass changes neither (`tools/` is outside it).

Differential suite (Icarus 12.0, macOS, `harness/sv/diff_test2.py --sim
iverilog`): 153 cases, 113 verified, 16 declared simulator
disagreements (14 before plus `concat_undriven` and
`array_param_labels_l7`), 23 unavailable backends (the sixteen crashes now
recognized), 24 skipped in all (the 23 plus the `xrun_only` row `t2_ci`), 0
failed, 0 ERROR, exit 0 (before: 16 ERROR rows on this host). Register:
`harness/divergence_register.py` OK, 3 live rows (sv 2, es 1), every live
guard held; `--self-test` OK.

## Default-point folds, static labels and nets (WP1) — 2026-10-28

Round-1 verifiers found three places where sv-0.2 symbolic mode gave a
SILENTLY wrong value — no refusal, disagreeing with Icarus 12.0 and with
Yosys 0.53 or the LRM — each a fact read off slang's DEFAULT-point
elaboration (a library module at its own defaults, a generate body at its
first iteration). All three are now exact or loud
(`docs/sv-envelope-schema.md`, "Default-point folds, static labels and
nets"); a fourth, a mislabelled refusal, is relabelled.

**(a) Unsized INT-class constants — exact.** `assign o = -1;` into a
parameter- or genvar-width target is an implicit conversion of the 32-bit
signed constant to the DEFAULT point's target type, and `_sym_conversion`
fell through to the M0 fold: a literal of that width, zero-extended by Lean
everywhere else (`w_stale_flat`: `[N+1:0]` at N = 7 read `000111111`, every
tool `111111111`; `w_gvw_flat`: `001011` for `111111`; `v_cstale`: a child at
`W = 8` read `00000011`/`00000001` for `-1`/`37`, every tool
`11111111`/`00100101`). The extractor now emits the UNCONVERTED INT-class
tree (`_sym_int_value_tree`, `_sym_int_value_node`: `Int`, `GenvarRef`,
unqualified `ParamRef`, unary `- + ~`, integer arithmetic in value or
constant spelling) — the `_sym_port_actual` treatment — whenever the
conversion is SIGN-PRESERVING: an assignment-like `Implicit` conversion
(the right-hand side keeps its own signedness, IEEE 1800-2023 §10.7,
§11.8.2) or a `Propagated` one into a signed type. `fitExpr2` materializes
it at the instantiated width. A `Propagated` conversion into an UNSIGNED
type zero-extends a negative operand and stays `ConversionExpression:width`.
A sized signed literal is a `SignedResize` of the literal at its own width
(`_sym_signed_literal_conversion`; it, too, used to fold at the default
width). Every other signed constant (`(3 > 2) ? -1 : 2`) is LOUD in a
parametric family (`ConversionExpression:signed-constant`,
`_sym_family_point_dependent`: an overridable parameter or an enclosing
genvar) and keeps the exact fold in a one-point module. Side effect: INT
expressions over parameters in value positions (`assign o = N - 1;`,
`o = K;`, `B * 2` with a `byte` B, `S < 0` with a `logic signed [3:0]` S),
which were `ConversionExpression:width`, are now admitted. No committed
envelope changed under (a).

**(b) Static labels over a parameter-dependent range — exact.**
`_sym_array_select_depth1` chose "canonical `[msb:0]`" at the default point
only, so `t[1 +: 2]` on `logic [K-1:0] t` (`K = N - 4`) and `v[1]` on
`[N-1:0]` kept the legacy `PartSel`/`BitSel` encoding, which reads a label
as an offset from lsb 0 at every point — wrong where the range is the
ascending `[-1:0]` (`vq_k0` at N = 4: `o = x0`, every tool `xx`; `vn_n0` at
N = 0). A select whose labels are all STATIC (literals, parameters,
localparams, enum members, `$bits` queries — `_sym_label_static`) over a
dimension whose declared bounds are not both literals is now an `ArraySel`
path, normalized against `IEnv.dims` at every point. Exact rather than loud
because the ∀-N proofs go through under their existing hypotheses, and
because a loud Lean-side guard is not available without changing theorem
statements: `instExpr2_bitSel_ident`, `instLhs2_bitSel`,
`fitExpr2_bitSel_ident` (Gen2) pin label = offset for EVERY environment, and
a declaration-level guard would falsify `ripple_elems`/`ripple_decls`, stated
for every `N : Int` although `a`, `b`, `s` are `[-1:0]` at N = 0 (where no
select on them is instantiated). Envelopes regenerated (10): `mul2d`,
`partsel`, `ripple_add`, `ripple_fa`, `sem2/ff_one`, `sem2/hier_nested`,
`sem2/hier_params`, `sem2/hier_width`, `sem2/probes/t2_sel`,
`sem2/register_file_ff` (their 36 rows pass unchanged). Proofs: the
envelope-shape pins `ripple_static_source` (`ripple_add`, `ripple_fa`) and
the `mul2d` templates `s0T`/`c0T`/`t0T`/`pHiT` follow the new tree;
`ripple_static` (both) and `mul2d_static` are re-proved with UNCHANGED
statements (`c[0]`, `c[N]` over `[N:0]` are in range for every `N : Nat`;
`s[0]`, `c[0]`, `t[0]`, `pp[0]` and the target `p[2*N-1:N]` under the
existing `1 ≤ N`), through new `mul2d` lemmas `mul2d_p_dims`, `evalInt_pMsb`,
`mulEnv_p` and the private `instExpr2_fill_ctx`. Every headline statement
(`ripple_processes`, `mem_ripple_processes`, `ripple_sem_*`, the
`ripple_add` spec/proof, `mul2d_processes`, `partsel_*`, `ripple_fa`) is
unchanged; `#print axioms` stays within `[propext, Classical.choice,
Quot.sound]`.

**(c) Nets — loud.** A net's undriven bits read z (§6.6) and the semantic
tier initializes every declaration to x; implicitly typed nets with packed
dimensions were already loud (`packed: null`), but scalar implicit nets and
explicitly typed ones passed the gate (`v_undf`, `v_undn`, `v_partnet`:
`zz`/`z0` read as `xx`/`x0`; a scalar `wire w`/`output wire yo` too). An
internal `wire` that would pass is now `NetSymbol:net-z`, an output port
whose internal symbol is a net (`output wire logic`, `output wire`, the
implicit `output y`) `PortSymbol:net-z` (`_sym_net_z`). Input net ports stay
admitted. No committed sv-0.2 envelope declares either.

**(d) Array-query labels.** `v[$bits(a) - 1 -: 2]` was refused and
mislabelled `RangeSelectExpression:dynamic-signed-base` because
`_sym_tree_static`/`_sym_reads_signal` read the query's argument as a
run-time value. A `$bits` query of a declared signal whose declaration
carries its width per point is now static (exact `ArraySel`, also as a
target and under `$clog2`; narrowed in the repair round below — the first
version admitted ANY argument); `$high`/`$size` of a signal are refused as
`…:query-label` (the constant tier reads them as `width - 1`/`width`, exact
only on a 1-D `[W-1:0]` range at every point) and keep the legacy encoding
where they had it (cv32e40p `alu_div`'s `OpA_DI[$high(OpA_DI)]`).

**Harness.** `harness/sv/diff_test2.py` gains LOUD-REFUSAL rows: a case
with a `refusal` kind passes only when the runner refuses the design at the
row's parameters and the kind appears in its error or in the envelope's
`Unsupported` kinds; it runs no simulator and counts as a refusal, never a
match (the summary line gains `N loud refusal(s)`).

**Recorded, not fixed (open).** (1) Labels that mention a GENVAR or read a
SIGNAL keep the legacy encoding, so at a point where the declared range is
not `[m:0]` with `m ≥ 0` they still read the label as an offset: on
`logic [N-1:0] v` at N = 0, `for (genvar g = 0; g < 2; g++) y[g] = v[g];`
and `o = v[s];` give `y = 10`, `o = 1` where Icarus gives `x0`, `x`
(silent). The route: genvar labels through `ArraySel` (template lemmas
re-stated under geometry hypotheses, as `mul2d`'s `MulEnvOk` does) plus a
run-time element `ArraySel` read. (2) NEW, outside this package, silent: a
`Resize` wrapping a CONTEXT-DETERMINED operand is lowered by
`instExpr2`'s `.resize` arm at the operand's own width and zero-extended,
while §11.6.1 evaluates the operation at the context width: `assign c =
a + b;` (4-bit `a`, `b`; `logic [N-1:0] c`, default N = 2, tree `Resize(2,
a + b)`) at N = 8 with `a = 1111, b = 0001` gives `00000000`, Icarus
`00010000` (`d = a - b`: `00001111` for `11111111`). A fix fits a
non-rigid, context-sized operand at the context when the context is wider
(not comparisons/reductions); among the ∀-N envelopes only `partsel` holds
a `Resize`. (3) `$high`/`$size` of a declared signal in the constant tier
are `width - 1`/`width` (Param.lean), wrong for a non-`[W-1:0]` range and
for `$size` of a multi-dimensional array; only the `crossCheck` at the
defaults catches it where the result is a localparam or a width. (4) NEW,
silent, pre-existing (the original extractor emits the same tree): a signed
parameter of a non-`int` type in an UNSIGNED context that is exactly as
wide as the parameter at the defaults — `assign o8 = a + B;` with a
`byte B = -3`, a 4-bit `a` and `logic [N:0] o8`, default N = 7 — needs no
conversion there, so the tree holds a bare `ParamRef B`, which Lean
sign-extends at a wider point while §11.8.2 zero-extends it (N = 40, a = 0:
Icarus `0…011111101`, model `1…111111101`).

Differential suite (Icarus 12.0, macOS, `python3 harness/sv/diff_test2.py
--sim iverilog`): 190 cases, 144 verified, 16 declared simulator
disagreements, 23 unavailable backends (24 skipped with the `xrun_only` row
`t2_ci`), 6 loud refusals, 0 failed, exit 0. Re-extraction of every
regenerable sv-0.2 envelope reproduces the committed bytes (124 same, 0
diff; the 3 cv32e40p envelopes whose sources are elsewhere skipped).

Differential rows (Icarus 12.0): `int_const_flat` (N = 7, 1, 2, 31, 40 and
N = 12 with `B = 100`; Yosys 0.53 agrees at N = 1 and N = 40),
`int_const_gen`, `int_const_hier`, `int_const_sized` (N = 7, 1, 30, 40),
`label_k0` (N = 8, 4, 5, 3, 2), `label_n0` (N = 4, 0, 1, 2, -1),
`label_param` (six `(N, P)` points), `bits_labels` (N = 6, 3, 9; Icarus 12.0
aborts on the out-of-range target at N = 1, 2, where the model agrees with
Yosys 0.53); loud-refusal rows `int_const_loud`, `net_z_flat`,
`net_z_scalar`, `net_z_hier`, `net_z_part`, `high_label`. Extractor tests:
`extractors/sv/test_symbolic_default_point.py` (15); two
`test_symbolic_continuous_selects.py` cases now expect the `ArraySel`
encoding of a literal label over `[W-1:0]`.

### WP1 repair round (verifier round 2) — 2026-10-28

The independent verifier found that the first version of (d) had opened a
new silent path, and three PRE-EXISTING silent default-point folds of the
same class. All four are now loud or exact; two smaller findings are fixed
and the open residual stays recorded.

**`$bits` labels, narrowed (regression of (d)).** `_sym_tree_static` and
`_sym_label_static` treated `$bits(x)` as static for ANY argument, and Lean
evaluates it from `x`'s instantiated declaration — whose width is a
default-point literal for a packed struct/union over parameter-dependent
members. Labels that used to be refused were admitted and wrong at every
other point (verifier `vg1`: `v[$clog2($bits(s)) +: 2]` and the target
`y[$bits(s) - 1 -: 2]` at N = 1, 2, 5, 8, 20; `vd1_p1`; `vj1`, a packed
union; Icarus and Yosys agree with each other). `$bits` is now static only
when `_sym_bits_query_exact` holds: its one argument names a variable or
net whose type is a scalar, a packed vector over explicit ranges or a fixed
typedef, an enum, or a packed struct/union whose layout is fixed at every
point. Any other `$bits` label — an expression, a part-select, a
point-dependent aggregate — is `…:query-label` (`_sym_inexact_bits_label`
in `_sym_array_select`; `_sym_has_value_query` for converted trees). Rows:
`bits_struct_fixed_n{1,2,4,9}` (exact), refusal rows `bits_aggregate`,
`bits_expr_label`.

**Point-dependent declaration shapes (pre-existing, root cause of the
above).** A packed struct/union is stored as one `[W-1:0]` vector with fixed
member `PartSel` windows, and a fixed unpacked array as one declaration per
DEFAULT-point cell, so a member, element or dimension width that depends on
an overridable parameter or a genvar was the default layout everywhere
(`vg2`: `s.x` at N = 8 read `00000101`, Icarus and Yosys `10110101`; `vb4`:
`mem[1]` of `[0:K-1]` at K = 1 a phantom cell that kept `d[3]`, Icarus
`xx`). The HEAD extractor emitted the same trees. `_sym_syntax_point_dependent`
walks a declaration's type and dimension syntax, following localparams,
typedefs and declared signals to their own declarations (package members
are fixed; anything it cannot classify counts as dependent), and in a
parametric family such a declaration is now `Unsupported`:
`…:default-point-aggregate` for a struct/union variable, net or port,
`VariableSymbol:default-point-array` for an unpacked array (its unpacked
dimensions, or a typedef'd element whose ranges were read off the canonical
type). A parameter typed with such an aggregate gets an unrecoverable type
(`packed: null`, refused by `crossCheck`). Refusal rows `aggregate_point`,
`array_point`, `aggregate_param`. No committed envelope changed (re-extraction
134 same).

**Case comparison width (pre-existing, Lean).** `instStmt2` lowered every
`case` item at the SUBJECT's self-determined width, while §12.5 compares at
the widest of subject and items: an unsized item was truncated to a
narrower subject — `case (b) -1:` on a 2-bit `b` matched `b = 2'b11` and
`4:` matched `b = 0`, at the DEFAULT point too (Icarus: no match), and the
verifier's `va2` (`case (a) -1:` on `logic [N:0] a`, default N = 40) matched
21 ones at N = 20 (Icarus, Yosys: 0). The envelope's subject `Resize`
carries only the default point's width. `Param2.lean` now lowers through
`caseWidth2` (the maximum over subject and items at the current point) and
fits the subject to it (`fitExpr2`: zero-extension; a `$signed` subject
needing a widening is loud). `case … inside` compares pairwise (§12.5.4), so
it keeps the subject's width when no item is wider and is otherwise loud
(`Case:inside-width`; Icarus 12.0 does not parse `case … inside`). Every
committed case statement has items no wider than its subject, so no
existing lowering changed; the `pCaseW` `#guard` in `Param2.lean` pins the
rule. Rows `case_width_n{1,2,3,20,32,33,40}` (exact), refusal row
`case_inside_width`.

**Smaller findings.** (1) `ConversionExpression:signed-constant` is used
only for a signed operand that reads no signal (`_sym_tree_static`); a
signed operand that does (`$signed(a) * -2` into `[N:0]`) is again
`ConversionExpression:width`, as at HEAD (refusal row `signed_operand`).
(2) The static-label routing of (b) exposed a second Icarus 12.0 reading
of constant-base `-:`: over a multi-element ASCENDING range, a select whose
base is the left label and whose width is the element count reads the whole
vector (`t[-1 -: 2]` over `[-1:0]` is `t[-1:0]`; the LRM, Yosys 0.53 and slang
read `{x, t[-1]}`). Declared (`iverilog-ascending-full-width-minus-select`,
row `label_kminus_w1`, `docs/sv-oracle-disagreements.md`, "Ascending
full-width minus select"); the family's other points pass
(`label_kminus_w{4,3,0,m1,5}`). (3) The three envelopes whose sources are
not on this machine (`Examples/system-verilog/{ff_one,alu_div,popcnt}`)
predate (b) and still carry legacy `BitSel`/`PartSel` encodings for static
labels; every claim their `ingest.lean` makes sits at a canonical point
(`LEN = 8, 32`; `alu_div` at `[8, 3]`, `[32, 6]`; `popcnt` at its defaults)
plus the point-independent `instantiate_WFNames`, where that encoding is
exact. They are to be regenerated when the sources are available (and
their `ingest.lean` cannot build while the umbrella `LeanModels` is red).
(4) Pin statements whose TEXT followed the regenerated envelopes in (b):
`ripple_static_source` (`ripple_add`, `ripple_fa`) and the `mul2d`
templates `s0T`/`c0T`/`t0T`/`pHiT`; no headline ∀-N statement changed.

**Still open (recorded, not fixed).** Genvar and signal (run-time) labels on
a parameter-dependent range keep the legacy offset encoding, so at a point
where the range is not `[m:0]` with `m ≥ 0` they read the wrong bit
(`vb3`: `o = v[s]` on `logic [N-1:0] v` is `1` at N = 0 and `0` at N = -1,
Icarus `x`). A Lean-side guard would falsify `instExpr2_bitSel_ident_dyn`,
`instLhs2_bitSel_dyn` and the genvar template lemmas, stated for every
environment; refusing every run-time bit-select on a parametric vector in
the extractor would refuse correct designs at every realistic point (`N ≥
1`). The route stays the recorded one: genvar labels through `ArraySel`
under geometry hypotheses, plus a run-time element `ArraySel` read.

Measured after the repair round: `python3 harness/sv/diff_test2.py --sim
iverilog` — 214 cases, 160 verified, 17 declared simulator disagreements,
23 unavailable backends (24 skipped with `t2_ci`), 13 loud refusals, 0
failed, exit 0 (new rows: `bits_struct_fixed_n*`, `case_width_n*`,
`label_kminus_w*`; refusal rows `aggregate_point`, `bits_aggregate`,
`bits_expr_label`, `array_point`, `aggregate_param`, `case_inside_width`,
`signed_operand`). Re-extraction of every regenerable sv-0.2 envelope: 134
same, 0 diff, 3 skipped. The verifier's repros `vg1`, `vg2`, `vd1_p1`, `vj1`,
`vb4` are refused at every swept point; `va2` (N = 20, 31, 32, 40, 50) and
`vd2` (N = 0, 1, 2, 3, 4, 7) pass against Icarus 12.0. Extractor tests
`test_symbolic_*.py` + `test_module_hierarchy.py`: 155 passed (eight new in
`test_symbolic_default_point.py`).

## One driver per bit on instance-free tops (WP2) — 2026-10-28

F3's one-driver rule (`driversOk`, `Hier2.lean` "Drivers", round 1) was
applied to every CHILD of a hierarchy and to a top only when the top held
an instance, so an instance-free top relied on the extractor's overlap
guard alone (`_symbolic_target_windows`), which sees literal-index windows
at the default point only — the gap recorded as (2) under "Module instances
in sv-0.2 symbolic mode" above. A flat top whose continuous drivers overlap
through a genvar or a parameter was admitted and resolved by issue order:
`for (genvar i = 0; i < 4; i++) assign y[i/2] = a[i];` loaded and gave
`y = xx00` at `a = 0101`, where Icarus 12.0 refuses the design
("Unresolved net/uwire y cannot have multiple drivers") and Yosys 0.53
reports "multiple conflicting drivers" — a design a ⊨₂ proof could have
been stated about while every oracle disagreed with it.

**The rule now covers every top, at every parameter point.**
`PDesign.instantiateG2` is `instantiate2` under `PDesign.driverGuard` (the
same rule, at the module's own signals), and `PDesign.instantiateGD2` is
its total family. `load_design_sv2` defines the flat `name.sem` as
`PDesign.instantiateGD2 name.pdesign [P₁, …]` (and so for a hierarchical
envelope whose top holds no instance in any generate branch),
refuses at elaboration time an envelope that violates the rule at its
defaults (message naming the signal and the clause), and the differential
runner instantiates a flat envelope through `instantiateG2` and reports
`PortConn:driver: <message>`. `instantiateH` is unchanged (its top guard
still checks a top with an instance; `instantiateH_flat` and every other
statement stand). One refinement of the rule's windows: an element select
with a LITERAL index (`Lhs2.index n (.lit c) ew`, `c` without x/z) now
drives element `c`'s window instead of the whole signal (`Lhs2.indexWin?`)
— exactly what `resolveLhs2` writes and `Comb2Base`'s `Lhs2.window?` names;
the sv-0.2 instantiation folds constant indices to slices, so no
instantiated design changes.

**What it does not refuse.** (Superseded the same day by the repair round
below, which adds the `always_comb`/`always_ff` exclusivity clause and
makes the §6.5 mixture clause per window.) Several PROCEDURAL writers of one variable
are not checked — Icarus accepts them, and the exclusivity rules for
`always_comb`/`always_ff` variables (IEEE 1800-2023 §9.2.2.2, §9.2.2.4)
are applied by tools per longest static prefix (§11.5.3), so writers of
distinct constant elements are legal. The one committed design with
several procedural writers of one variable,
`sem2/register_file_ff` (generate-indexed `always_ff` writers of distinct
`mem` elements), stays admitted. A continuous driver of a procedurally
written variable (§6.5's forbidden mixture) and any write to an input port
(§23.3.3.2) remain refused, as in round 1. Scanned with the new families:
every committed sv-0.2 envelope at its defaults and every `cases2.json`
point — no committed envelope, `load_design_sv2` user or differential row
changed status; the only `PortConn:driver` refusals are the new rows below.

**Proofs: statements unchanged, guard discharged.** Every ∀-N proof through
`name.sem` now removes the guard, with these new lemmas (`Hier2Gen.lean`):

* `PDesign.instantiateGD2_of_ok` — the instantiation at the surface fuel
  plus `driversOk` on its process list give `name.sem … = m`;
  `PDesign.instantiateGD2_of_driversOk` (the same, stated on
  `instantiateD2`), `PDesign.instantiateGD2_eq_driverGuard` (at any point),
  `PDesign.instantiateG2_of_ok`, `Design2.errorDesign_driverGuard`.
* The reusable route from the comb profile:
  `driversOk_of_combDesign` (a `CombDesign` with positive write windows
  passes `driversOk` at any names and any list of its input ports —
  `CombDesign.disjoint`/`selfDisjoint`/`notInput` ARE the rule's clauses,
  carried to the driver windows by `DrvWin.MatchList` /
  `Lhs2.drvWins_matchList` and `DrvWin.overlaps_eq_false_of_matches`) and
  its flat-family corollary `PDesign.instantiateGD2_of_combDesign`, with
  `PDesign.instantiate2_inputNames`. Demonstrated on the proved design
  behind `sem2/concat_add` (`cadd_driversOk`, from `cadd_comb` alone).
* The process-list route: `driverWins_map` (with round 1's
  `driverWins_cons`/`_append`/`_flatMap`), `DrvWin.overlaps_some`,
  `DrvWin.overlaps_some_eq_false`, `DrvWin.overlaps_none_left`/`_right`,
  `pairwise_flatMap_range` (a generate family's windows: one cell, and two
  cells `j < k`) and `rowMajor_le` (row-major bases `i * K` for `omega`).

Discharged: `ripple_add/gen.lean` (`ripple_driversOk`, every `N`;
`ripple_sem_eq : ripple_add.sem N = ripple_add.pdesign.instantiateD2 [N]`
re-proves `ripple_sem_processes`, `mem_ripple_sem_processes`,
`ripple_sem_decls`, so `proof.lean`/`spec.lean` are untouched) and
`mul2d/gen.lean` (`mul2d_driversOk`, every `N`: rows stated over their
base offsets, `rowMajor_le` between rows; `mul2d_processes` re-proved).
`partsel/gen.lean` and the eight `sem2/*/agree.lean` relate `name.sem` by
`#guard` at concrete points, which pass unchanged; `ripple_fa` is
hierarchical (round 1's `ripple_fa_driversOk`).

**Recipe for a svGolf proof** (`Hier2Gen.lean` module docstring): prove
the instantiation `pd.instantiate2 [N] (PDesign.surfaceFuel [N]) = .ok m`
(the `Gen2.lean` recipe), then either (a) `CombDesign m` — which the settle
theorem needs anyway — and positive write windows:
`PDesign.instantiateGD2_of_combDesign h hc hpos : name.sem N = m`; or (b)
the process list `P N` of `m`, its windows by `simp only [driverWins_cons,
driverWins_append, driverWins_flatMap, driverWins_map, Process2.drvWins,
Lhs2.drvWins, List.filter_cons, …]`, disjointness by
`pairwise_flatMap_range` + `simp [DrvWin.overlaps]` + `omega`, and
`driversOk_of_continuous` → `PDesign.instantiateGD2_of_ok`. Then rewrite
every `name.sem N` fact along the equation.

**Rows** (`harness/sv/cases2.json`, sources `Examples/system-verilog/sem2/drv_*`):
`drv_genvar_ov` (the probe, loud `PortConn:driver`), `drv_genvar_disj`,
`drv_genvar_disj_n1`, `drv_genvar_disj_n3` (`y[2*i +: 2]` over a genvar and
`N`: admitted, PASS against Icarus 12.0), `drv_param_ov` (`y[K+1:K]` next
to `y[1:0]` at `K = 2`: PASS), `drv_param_ov_k1`, `drv_param_ov_k0` (the
same envelope at `K = 1, 0`: loud). In-Lean pins: `Hier2.lean` `#guard`s
`flatLoud` (`pGv`, `pParOv`, `pDrvTwice`, `pDrvIn`).

**Doc fixes (round-1 leftovers).** `Comb2Base`'s `Lhs2.window?` docstring
no longer calls concatenation targets out of profile (they are in, through
`Lhs2.windows?`); `Comb2Proc`'s covered-shapes text qualifies
"`unique`/`priority` do not change execution" — true in simulation (Lean,
Icarus, §12.5.3), not after Yosys 0.53 `proc` (a `unique`/`priority` case
with no matching arm is don't-care; x bits in plain `case` item constants
are wildcards; `docs/sv-oracle-disagreements.md`); its gaps paragraph
records that a block-local declaration inside `always_comb` reaches the
envelope as `LocalDecl`, which the sv-0.2 ingestion refuses, and that
`unique if`/`unique0 if`/`priority if` are refused by the extractor
(`ConditionalStatement:Unique`/`:Unique0`/`:Priority`).

Measured: `python3 harness/sv/diff_test2.py --sim iverilog` — 221 cases,
164 verified, 17 declared simulator disagreements, 23 unavailable backends
(24 skipped), 16 loud refusals, 0 failed, exit 0 (new: 4 verified, 3 loud).
A scan of all 141 committed sv-0.2 envelopes at their defaults and all 221
case points through `instantiateG2`/`instantiateH`: `PortConn:driver` only
on `drv_genvar_ov` (defaults and row) and `drv_param_ov` at `K = 1, 0`.
Re-extraction of every regenerable sv-0.2 envelope: 137 same, 0 diff, 3
skipped (the three new envelopes included). The ∀-N proofs and every
`load_design_sv2` user build with unchanged statements; the new theorems'
`#print axioms` are within `[propext, Classical.choice, Quot.sound]`.

### WP2 repair round (verifier round 2) — 2026-10-28

Three verifier findings, all fixed.

**(1) Procedural writers of one bit were admitted and silently ordered.**
WP2's rule checked continuous drivers only, so two `always_comb` (or
`always_ff`) processes writing one bit — illegal under IEEE 1800-2023
§9.2.2.2/§9.2.2.4, an error in slang's full analysis
(`-Wmultiple-always-assigns`) — loaded and ran with `Sem2`'s process order
deciding the bit: `always_comb y[0] = a[0]; always_comb y[0] = a[1];` gave
the second block's value where Icarus 12.0 gives the first's; a genvar- or
parameter-dependent pair (`always_comb y[i/D] = a[i]` at `D = 2`,
`y[K]`/`y[0]` at `K = 0`) and two generate-loop `always_ff` writers
diverged the same way (verifier rows `pw_lit`, `pw_ov`, `pw_par`, `pw_ff`;
for the flop pair neither `σ_src` nor `σ_rev` matched Icarus). Round 1's note that "slang and the extractor report it at
the default point" was wrong: the extractor never runs slang's driver
analysis. `driversOk` gains a fourth clause, `procExclusiveOk`: no window an
`always_comb`/`always_ff` process writes (`Process2.exclusive`;
`Process2.procWins` = `Stmt2.drvWins` of its body, every branch, a run-time
index the whole signal — exactly the longest static prefix, §11.5.3) shares
a bit with a window ANY other process writes (`Process2.exclClash`). Two
plain `always @(posedge clk)` writers stay admitted (legal; Icarus runs
them). `alwaysFFR` counts as exclusive because it does not record whether it
came from `always_ff` or from a plain `always @(posedge clk or negedge rn)`:
two plain async-reset writers of one bit are refused although legal — a
conservative LOUD over-refusal; no committed envelope or row has one.

**(2) The §6.5 mixture clause was per signal.** WP2 refused a continuous
driver of ANY bit of a procedurally written variable, which also refused
legal flat designs Lean had simulated exactly like Icarus
(`always_comb y[0] = a; assign y[1] = b;`), and the docs cited §6.5 for
it although §6.5 forbids the mixture only on one longest static prefix. The
clause is now per window: a continuous window must share no bit with any
procedural window (`driversOk`'s second clause). The input-port clauses
stay per signal (any write of an input port is §23.3.3.2's).

**(3) Default-point cell indices (extractor, pre-existing).** A constant
element select into a fixed unpacked array names its cell, and slang's
constant for `m[i]` (genvar) or `m[K]` (overridable parameter) is the
DEFAULT point's: `for (genvar i …) assign y[i] = m[i];` read `m[0]` at
every `i` (y = 0000 at a = 0110, Icarus 0110), `assign m[K] = a;` wrote
`m[0]` at every `K` (at `K = 1` Icarus gives `zz1z`). WP2's rule had only
made the multi-iteration WRITE form loud by accident (two drivers of
`m[0]`). Additive extractor hook `_sym_cell_index_point_dependent` (five
one-line call sites: the cell-name helper, both out-of-bounds helpers, the
symbolic select read, and both assignment converters): in a parametric
family a constant select INTO an unpacked dimension whose index names a
genvar or an overridable parameter is `Unsupported`
(`ElementSelect:default-point-index`), read or write. Literal and localparam
indices, run-time indices and a genvar bit-select inside a cell
(`m[0][i]`) are unchanged; M0 mode never reaches it (`_SYM is None`).
Pinned by `extractors/sv/test_symbolic_cell_index.py` (6 tests).

**Proofs.** No statement changed. `Process2.procWrites` is now
`procWins.map (·.1)` (the same value), `driversOk_of_continuous` is
re-proved from its unchanged hypotheses (the new clauses hold vacuously
without procedural windows: `procWins_nil_of_procWrites`,
`procExclusiveOk_of_procWins_nil`), and so every route of WP2 —
`driversOk_of_combDesign`, `PDesign.instantiateGD2_of_combDesign`,
`ripple_driversOk`, `mul2d_driversOk`, `ripple_fa_driversOk`,
`cadd_driversOk` — builds untouched. New for designs WITH procedural
processes: `driversOk_iff` (the rule clause by clause, as `Pairwise` /
`∀ … ∈` statements), `procExclusiveOk_iff`, and
`Process2.exclClash_of_procWins_nil_left`/`_right` (a continuous assign
clashes with nothing). Recipe: `driversOk_iff.mpr ⟨…⟩`, the windows by
`simp [driverWins_cons, …, Process2.procWins, Stmt2.drvWins,
Stmt2.drvWinsList, Lhs2.drvWins]`, generate families by
`pairwise_flatMap_range`, each pair by `DrvWin.overlaps_some_eq_false` +
`omega`.

**Rows** (sources `Examples/system-verilog/sem2/`): `drv_pw_lit` (two
`always_comb` on `y[0]`, loud), `drv_pw_gv` (genvar/parameter pair, loud at
`D = 2`) and `drv_pw_gv_d1` (pass), `drv_pw_par` (pass at `K = 1`) and
`drv_pw_par_k0` (loud), `drv_pw_ff` (two `always_ff`, loud at `D = 2`) and
`drv_pw_ff_d1` (pass), `drv_mix` (`always_comb y[0]` + `assign y[K]`, pass
at `K = 1`) and `drv_mix_k0` (loud); `cell_genvar`, `cell_param`,
`cell_param_k1` (loud `ElementSelect:default-point-index`) and the control
`cell_fixed`, `cell_fixed_w3` (pass). slang's full analysis refuses exactly
the loud driver points and accepts the passing ones. In-Lean pins:
`Hier2.lean` `pPw` (`flatLoud` at each clause, including a run-time index,
`always_ff`/`always` pairs, and one process writing a bit twice).

Measured: `python3 harness/sv/diff_test2.py --sim iverilog` — 235 cases,
170 verified, 17 declared simulator disagreements, 23 unavailable backends
(24 skipped), 24 loud refusals, 0 failed, exit 0 (new: 6 verified, 8 loud;
every earlier row keeps its verdict). A scan of all 148 committed sv-0.2
envelopes at their defaults and all 235 case points through
`instantiateG2`/`instantiateH`: `PortConn:driver` only on the `drv_*` rows
meant to be loud — `cv32e40p_register_file_ff`'s generate-indexed
`always_ff` writers (distinct constant `mem` elements) stay admitted, and no
committed envelope or `load_design_sv2` user has two writers of one window.
Re-extraction of every regenerable sv-0.2 envelope with the cell-index
hook: 145 same, 0 diff, 3 skipped (the new envelopes included). The ∀-N
proofs, the eight `agree.lean` files and every buildable `load_design_sv2`
user build with unchanged statements; the new theorems' `#print axioms` are
within `[propext, Classical.choice, Quot.sound]`.

## The multi-point cross-check (CX, round 3) — 2026-10-28

Rounds 1–2 closed a long tail of silent wrong values of ONE class: the
extractor elaborates a symbolic envelope with slang at the DEFAULT
parameter point, and something it computes there — a width, an offset, a
cell, a sign — leaks into the symbolic tree, so `name.sem P` is wrong at
other points `P` while every default-point check passes. Each was found by
a verifier and fixed by its own guard (`ElementSelect:default-point-index`,
`VariableSymbol:default-point-array`, `…:default-point-aggregate`,
`ConversionExpression:signed-constant`, …). This round replaces the
whack-a-mole with a check that makes the whole class loud at chosen points.

**The check.** `extract.py --top T … --probe-points "N=1;N=4,W=8"` re-runs
the SAME symbolic extraction with slang's top-level `paramOverrides` set to
each point (slang then elaborates the point itself) and writes the opt-in
sidecar `<file>.sv.probes.json` (`docs/sv-envelope-schema.md`, "Probe
sidecars"); the envelope stays byte-identical. Each instance of the
point-elaborated hierarchy is probed too (its definition re-extracted alone
at the overrides it receives there). `LeanModels/Sv/Probe2.lean`
(`PDesign.pointVerdict`, `PDesign.pointAgrees`) brings the envelope's
module and the point's module to the point with the same `atPoint`,
instantiates both with the same `instantiateG2`/`instantiateH`, and compares
the two `Design2` values (declarations exactly; processes in order,
structurally, after a width-identity normalization); it also replays the
point module's own `resolved` metadata at the point (the load gate's
Lean-vs-slang differential, extended to every probe point) and fails on
slang errors at the point. A fold differs between the two extractions, so
it is caught wherever it changes something.

**Verdicts.** `agree` (the only pass); `differ` — two VALUES differ, a
silent fold; `unconfirmed` — equal except where one side is LOUD (slang's
tree at the point holds a conversion the extractor does not admit, so
nothing vouches for the envelope's value there); `metaDiffer`,
`frontendRejects`, `refused`. A refusal on either side is never agreement.

**Consumers.** `load_design_sv2` runs every entry of a sidecar when one
exists and refuses the envelope at the first non-`agree` entry, naming the
point, the entry and the first differing declaration or process (and its
innermost differing node). `diff_test2.py --xcheck` (DEFAULT ON)
re-extracts every row with parameter overrides at the row's point (the
committed envelope must be byte-identical to the fresh extraction, else
`XCHECK-STALE`), and the runner prints the row point's verdicts
(`runner2.lean … <probes.json>`); any `FAIL` is `XCHECK-FAIL`, a failed
case; `UNCONFIRMED` passes only when every simulator then matches the model
at that very point. The svGolf checker calls `probeReportString` /
`probeCheckString` / `probeCheckFile` (`Ingest2.lean`; `probeCheckFile`
answers `.ok none` when no sidecar exists — nothing compared, not
agreement); `harness/sv/xcheck2.lean` is the command-line front end
(`--batch` for sweeps). Committed sidecars guard the ∀-N proof examples
`ripple_add` (N = 1, 2, 3, 5, 8, 16), `mul2d` (N = 1, 2, 3, 5, 8),
`partsel` (eight points over N and W) and `ripple_fa` (N = 1, 2, 3, 5, 8,
16, every `full_adder` instance included): all agree, their proofs build
with unchanged statements, and the load-time cost is below the noise
(partsel: 2.25–2.30 s with the sidecar, 2.28–2.38 s without).

**False mismatches, measured and removed.** Comparing the raw instantiated
trees, the sweep below reported 81 non-agreeing entries; 36 of them were
equal circuits written differently, all from one cause — slang inserts a
conversion exactly where the widths at ITS point differ, so the same source
carries a conversion that is the identity at one point and absent at the
other (`resize 4 a` against `a` with a 4-bit `a`; `resize 8 (c ? 0 : r)`
with a 32-bit `0` against `c ? 8'b0 : r`; `resize 4 (c & resize 6 b)`
against `resize 4 c & b`; a resize around an operand that is already loud).
`Expr2.norm` removes exactly those — an identity `resize`/`resizeSigned`
vanishes, a resize of a literal is evaluated, nested truncations merge, a
resize moves through a ternary or a bitwise `& | ^` whose operands have one
width, an expression with a loud operand is that operand (the evaluator is
strict in every operand) — each rule an equation of `evalExpr2` on
width-correct values; nothing moves through arithmetic, whose whole-vector
x-collapse sees the high bits (`#guard`ed both ways in `Probe2.lean`).
After it: 0 false mismatches.

**Measured** (every sv-0.2 envelope whose top has parameters and whose
sources are on this machine — 66 envelopes — at every parameter alone over
N ∈ {1..8, 16, 32} plus every `cases2.json` row's own point; one point
dropped whose declarations exceed 65536 bits; 967 points, 1145 entries with
178 instance entries):

| verdict | entries | what |
|---|---|---|
| agree | 1100 | |
| differ (silent fold) | 0 | none in any committed envelope |
| unconfirmed, point refuses | 30 | `context_divider`/`_16`, `context_power`/`_16` at W = 1..7 (`ConversionExpression:signed-constant` on `(-8'sh80) / 8'sd2` and `** 2`), `case_width` at N = 33, 40 (`ConversionExpression:width` on the item `N`); all 30 simulator-correct (Icarus 12.0: the 28 division/power points as scratch rows, the two `case_width` rows in the suite) |
| unconfirmed, envelope refuses | 1 | `int_const_loud` N = 32 |
| unconfirmed, both refuse differently | 3 | `const_wrap` K = 2, 3; `array_point` K = 1 |
| refused | 11 | `aggregate_param` at every N (the envelope itself refuses: unrecoverable packed dimensions); `register_file_ff` ADDR_WIDTH = 32 (generate fuel) |

Cost: extraction 45 ms per point (in process, 43.8 s for the sweep), the
Lean check median 1 ms, p90 6 ms, max 7.4 s per point
(`register_file_ff` at 256 registers); the whole sweep is one
`xcheck2.lean --batch` process of 19–33 s wall time (machine load).

**The check catches the folds of rounds 1–2.** With each guard disabled
again (monkeypatched to "never point dependent", scratch extractions) the
cross-check reports a SILENT difference at every non-default point where
the fold changes the design, and the current extractor agrees (or is loud
on both sides): `_sym_cell_index_point_dependent` (`cell_param`: the
envelope writes `m[0]`, slang at K = 1, 2, 3 writes `m[K]`),
`_sym_array_point_dependent` (`array_point`, K = 1, 3, 4: declaration
count 6 vs 5/7/8), `_sym_aggregate_point_dependent` (`aggregate_point`,
`bits_aggregate`, N = 1, 2, 4, 8: `s` 5 bits vs `N + 2`), and the
signed-constant guard (`int_const_loud`, N = 32). `load_design_sv2` of the
`cell_param` mutation refuses at K = 1 with "differ (SILENT default-point
fold): … envelope … (Lhs2.ident "m[0]") … ≠ point … ".
`extractors/sv/test_probe_points.py` pins the extractor half (byte-identical
envelope, recorded points and instances, refused points, the mutation
visible in the sidecar, every committed sidecar regenerating byte for
byte).

**Rows.** `xcheck_div_w4`, `xcheck_pow16_w3` (an `UNCONFIRMED` point the
simulator verifies). Every earlier row with overrides now also runs the
cross-check; `case_width_n33`/`_n40` are `UNCONFIRMED, simulator-verified`.
Measured: `python3 harness/sv/diff_test2.py --sim iverilog` with the
cross-check on (255 cases, the WP4 rows of the same day included): 181
verified, 17 declared simulator disagreements, 24 skipped (unavailable
Icarus backends), 33 loud refusals, 0 failed — of the 118 rows with
integer overrides, 107 run rows `xcheck:agree`, 4 `UNCONFIRMED,
simulator-verified` (`case_width_n33`, `_n40`, the two new rows), and the 7
loud rows report it for information (6 agree; `aggregate_param`'s envelope
refuses at its point). Seven cases first ERRORed on a missing `.olean`
while the other lane rebuilt `Param2`; each passed when rerun alone.

**Not covered — for WP FOLDS.** (1) A fold whose dependency is a GENVAR,
not a parameter: the extractor binds a generate-for body from its first
iteration at every point alike, so the multi-point check cannot see it
(the round-2 `cell_genvar` reads were found by a verifier, not by this).
A per-iteration check would compare slang's elaborated `genblk[i]` bodies
with Lean's substitution. (2) The `unconfirmed` class is over-cautious on
every measured case: the extractor refuses at the point a conversion it
would not need at the default (a signed constant narrowed into a W-bit
target; a 32-bit parameter widened to a 40-bit case subject); admitting
those conversions symbolically would turn 30 entries into `agree`.
(3) A hierarchy's child is checked at the overrides slang gives it, which
are not compared with the values `instantiateH` computes for it.
(4) `Expr2.norm`'s rules are argued and `#guard`ed, not proved (they run
in the checker only; a wrong rule could only hide a fold, never change
`name.sem`).

### CX repair round (verifier round 3) — 2026-10-28

The independent CX verifier returned `fix` with two majors and two minors
(and, as one of the majors, the round-2 WP2 verifier's two majors in Lane
B's extractor, which CX was asked to carry and had not). All are fixed;
no theorem statement changed.

**(1) The probe compilation elaborates the top alone.** slang applies
`paramOverrides` to EVERY top-level module of a compilation, and
`getAllDiagnostics` counts the errors of every one. A source set holding
an unrelated, uninstantiated module with a parameter of the same name
(`multi_top` beside `side_mod`, whose `if (N > 6) $error(…)` fires at
N = 8) made the point extraction report `frontend_errors = 1`, so
`xcheck2`, `diff_test2` (`XCHECK-FAIL`) and `load_design_sv2` all refused
a DUT that Icarus 12.0, Xcelium, Yosys 0.53 (`chparam; eval`) and
Verilator 5.042 run correctly at N = 8 (verifier evidence); the same cause
could inject `Division:/Remainder:/Power:/Shift:invalid-compilation`
markers into the point module. At a probe point `_sym_top_compilation(top)`
now sets `topModules = {top}` beside `paramOverrides`, and the
`frontend_errors` compilation shares it — a testbench's `#(.N(v))` and
`name.sem` override the DUT alone. The default-point envelope is still one
plain compilation of all sources (byte-identical). Fixture
`sem2/multi_top` (rows `multi_top`, `multi_top_n8`: PASS, `xcheck:agree`);
test `test_unrelated_top_neither_receives_the_point_nor_counts`.

**(2) The round-2 WP2 verifier's majors.** The CX report said the round-2
journal had no final `WP2:verify` result. That was wrong: the second
`WP2:verify` entry (key `v2:42213afc…`) has a `result` with verdict `fix`
and two majors in Lane B's extractor. Both are fixed here
(`docs/sv-envelope-schema.md`, "Declaration initializers"):

- *An output-port initializer was dropped.* slang keeps
  `output logic [1:0] y = 2'b10`'s initializer on the PORT symbol, not on
  the port's internal variable, and `convert_port_sym` never read it:
  `name.sem` gave `y = x1, x0` where Icarus gives `11, 10` (probe
  `vg_initq`). The `Port` node now carries it as an optional `init` (the
  key is absent without one), ingested (`Ingest2.parsePDecl`) into
  `PDecl.init` exactly like a `Var`'s; an output NET port with one (illegal,
  slang `DisallowedPortDefault`) is `PortSymbol:initializer`; the Lean
  side refuses an input `Port` carrying one (a port default stays the
  connection's `PortConnection:default`). This was the SAME at every
  point, so the cross-check could not see it: the parametric twin
  `vg_initqp` agreed at N = 3, 5 while wrong at every N.
- *An initializer plus a continuous driver was admitted.* A variable's
  declaration initializer is a procedural write (§10.5) the one-driver
  rule never sees, so `logic [1:0] t = 2'b10; assign t[0] = a;` mixes
  continuous and procedural writers (§6.5): slang `-Wmixed-var-assigns`,
  Icarus "Unable to assign to unresolved wires", Yosys 0.53 a conflicting
  constant driver — and the model ran it (`y = 11, 10, 1x`). A continuous
  driver of any bit of an initialized declaration is now refused: `assign`
  → `ContinuousAssignSymbol:initialized-variable` / `:initialized-net`,
  instance output connection → `PortConnection:initialized-variable` /
  `:initialized-net` (a net's initializer is itself a continuous driver,
  §10.3.1, so the extra driver is a resolved multi-driver net: Icarus gives
  `w[0]` = 1, x, x, 1 for `a` = 1, 0, x, z). Only the target PATH is
  walked (an index is read, not written); an output variable port's
  initializer is found on its port symbol; procedural writers
  (`always_comb`, `always_ff`) of an initialized variable stay admitted.
  (CORRECTED round 4, Lane A: Xcelium 24.03 rejects every `always_comb` /
  `always_ff` writer of an initialized variable, `*E,MULAXX`, so they are
  now refused, `ProceduralBlockSymbol:initialized-variable`; a plain
  `always` writer stays admitted. See "Declaration initializers, every
  form, and the always_comb/always_ff mixture (round 4, Lane A)" below.)
  The suggested `driversOk` alternative was not taken: the exclusivity
  clause and its theorems stay untouched. Before the guard the net form
  was already loud for an unrelated reason (a `wire [1:0]` net's packed
  dimensions are not recovered in symbolic mode); the variable, port and
  hierarchical forms were silent.

Rows (Icarus 12.0): `vg_initq`, `vg_initqp`, `vg_initqp_n1`, `_n3`, `_n5`,
`vg_initc` PASS; `vg_init`, `vg_initp` (`ContinuousAssignSymbol:
initialized-variable`), `vh_init` (`PortConnection:initialized-variable`),
`vg_initn` (`ContinuousAssignSymbol:initialized-net`) loud. Tests:
`extractors/sv/test_sym_initializers.py` (11). (Round 4, Lane A: the six
PASS rows are now loud refusals, `ProceduralBlockSymbol:initialized-
variable` — Xcelium 24.03 rejects an `always_ff`/`always_comb` writer of an
initialized variable; see the round-4 entry below.)

**(3) Untyped child parameters (minor).** An untyped parameter takes the
type of its final value (§6.20.2), so `uchild2 #(.P(4'd9))` has a 4-bit `P`
while the probe's integer override `P=9` gives a 32-bit signed one; the two
instances `#(.P(4'd9))` and `#(.P(9))` were merged into one int probe that
checked another family member. `_probe_int_typed` now records such an
instance unprobed (`overrides: null`, a loud `refused` entry): an untyped
parameter (implicit type, no range) is probed only when its type at the
instance is the 32-bit signed one. No silent consequence existed
(`instantiateH` already refuses a sized override of an untyped parameter);
test `test_untyped_sized_child_override_is_unprobed`.

**(4) Messages and the harness module list (minor).** Every non-agreeing
verdict used to print "the envelope and slang's extraction at this point
differ (a default-point fold)" (`diff_test2.py`) and "…something the
extractor computed at the defaults leaked…" (`load_design_sv2`), also for
`frontendRejects`, `metaDiffer` and `refused`, where nothing differed.
`ProbeVerdict.meaning` (`Probe2.lean`) now says what each verdict means
(only `differ` is a fold), `load_design_sv2` appends it, and `diff_test2`
prints a neutral `XCHECK-FAIL` headline above the verdict lines.
`SV_LEAN_MODULES` gains `CombGuard2` (after `Sem2`; `Param2` imports it),
so an edit to it rebuilds the harness's `Param2`/`Hier2`/`Probe2`/`Ingest2`.

The round-2 WP2 verifier's minor on `test_division.py::test_selected_
constant_positions_do_not_acquire_runtime_markers` (it still looked for
the `PartSel` that the round-2 static-label change turned into an
`ArraySel`) is fixed in the test: it reads the `ArraySel`'s `part.left`,
same assertion. Its other minors (`driversOk_of_lowerComb`, the per-cycle
`vg_plain2` race) are not Lane B's.

**Measured.** `reext`: same 161, diff 0, skip 3 (the cv32e40p envelopes,
sources off-machine) — no committed envelope had an output-port
initializer or an initialized continuous target. The CX sweep re-run with
the repaired extractor (68 envelopes — the 66 of CX plus `vg_initqp` and
`multi_top` — 987 points, 1165 entries): every one of the 1145 entries of
the CX sweep keeps its verdict (1100 agree, 34 unconfirmed, 11 refused,
0 differ) and the 20 new entries agree; extraction 39 ms per point (38.4 s
in all), the Lean batch 12.9 s wall. `python3 harness/sv/diff_test2.py
--sim iverilog` with the cross-check on, 271 cases (the WP4 rows of the
same day included): 189 verified, 20 declared simulator disagreements, 24
skipped (23 unavailable Icarus backends), 38 loud refusals, 0 failed, 0
errors; 111 row points `xcheck:agree`, 4 `UNCONFIRMED, simulator-verified`
(unchanged). Extractor suite `python3.12 -m pytest extractors/sv/`: 1744
pass, 3 skipped, 0 failed (`test_division` included). Builds (one slot command): the
SV modules, the ∀-N proof examples, the nine `agree.lean` files
and every non-umbrella `load_design_sv2` user, unchanged statements.

## The `always_comb` self-read guard (WP4) — 2026-10-28

**Decision (Thomas, 2026-10-28): refuse self-reading `always_comb` bodies,
loudly.** IEEE 1800-2023 §9.2.2.2.1 leaves out of an `always_comb` block's
implicit sensitivity list "any expression that is also written within the
block", so an event-driven simulator runs the block once per wake-up and a
read of a bit the block writes LATER sees the previous run's value; `Sem2`'s
`combSettle2` re-runs the block to its fixpoint. Icarus 12, Xcelium 24.03
and mox-sim show the stale value, Verilator 5.042, Yosys 0.53 and the settle
semantics the combinational one: no answer is safe. `sv-div-3` (declared the
same morning, `run2` keeps the settle answer) is RETIRED by this refusal.

**The rule** (`LeanModels/Sv/CombGuard2.lean`, `Stmt2.combViol`): a body is
refused when, on some control path, a bit is READ before the path writes it
AND the path WRITES that bit later — per bit, path-sensitive. A static walk
carries `M`, the bits written on every path so far (`Stmt2.mustW`: an `if`
without `else`, a `case` without `default`, a run-time index target and a
procedural concatenation must-write nothing), and `A`, the bits some path
may write after the current statement (`Stmt2.mayW`: a run-time index may
write all of its signal); a read outside `M` that the current assignment or
`A` may write is a violation. Conditions are independent (a body has no
loops, so every path through a point is a prefix times a suffix), which
makes "outside `M`, inside `A`" exactly "some path reads it unwritten and
writes it later". Reads: `if` conditions, `case` subjects and patterns,
right-hand sides, the index expressions of reads and targets (and the
operands of a compound assignment once lowered — the symbolic extractor
still refuses `+=` itself, `AssignmentExpression:compound`). A constant
slice reads/writes exactly its bits; after instantiation every constant
index IS a constant slice (`instExpr2`/`instLhsLeaf2`), so constant indices
are decided exactly and every `.index` is a run-time one, treated as a
may-overlap with the whole signal. Refused: `y = t; t = a;`,
`if (c) t = a; y = t; t = b;` (the `c = 0` path; Verilator's ALWCOMBORDER
misses it), `t[0] = a; y = t[1]; t[1] = b;`. Admitted: a latch
`if (en) q = d;`, a latch reading its held value `if (en) q = d; y = q;`,
`t[0] = a; y = t[0]; t[1] = b;`, temporaries written on every path first.

**Process kinds.** `combSettle2` re-runs the comb-phase kinds
(`Process2.isCombPhase`): `alwaysComb`, continuous `assign`, and the loud
`unsupported`. Only `alwaysComb` runs once per wake-up in a simulator, so
only it is guarded; a continuous `assign` is re-evaluated on every change of
its right-hand side, its own writes included, in both readings, and
`always_ff`/plain `always @(posedge …)`/`alwaysFFR` run once per edge in
both. `always @*`, `always @(a or b)`, `always @(a)` and `always_latch` never
reach `Process2` in symbolic mode — measured: `TimedStatement:
ImplicitEventControl`, `TimedStatement:EventListControl`,
`SignalEventControl:None_`, `ProceduralBlockSymbol:AlwaysLatch` — so there
is nothing else to cover; if one is admitted later as a comb-phase process
it must go through `combGuardProc` too.

**Where.** Per process, where every instantiated `always_comb` is built:
`instProcess2` (`Param2.lean`) now maps `PProcess.alwaysComb b` to
`combGuardProc (env.widths.lookup) (instStmt2 env elems b)` — the process
itself when admitted, else `Process2.unsupported "AlwaysComb:self-read" msg`,
whose message names the signal and the bits and cites §9.2.2.2.1. That is
every parameter point of every `name.sem` (flat `instantiateGD2`,
hierarchical `instantiateHD2`, generate-expanded, every child module), the
differential runner's design, and `load_design_sv2`'s defaults gate, which
refuses with the same message (an arm next to `PortConn:driver` in
`Ingest2.lean`, naming the top module). DEVIATION from the plan (a hook next
to `Design2.driverGuard`/`PDesign.topGuard` in `Hier2.lean`): every guard
composed there is pinned by theorems whose statements must not change —
`Design2.driverGuard_of_ok`, `PDesign.instantiateG2_of_ok`,
`PDesign.instantiateGD2_of_ok`, `PDesign.instantiateGD2_of_driversOk`,
`PDesign.instantiateH_of_rec` all conclude "the guarded family IS the raw
instantiation" from `driversOk` alone, and folding the rule into
`driversOk` falsifies `driversOk_iff`. A per-process hook inside
`instProcess2` keeps every one of them true (no generic lemma computes
`instProcess2` of an `alwaysComb`), and no ∀-N proof needed a change. The
process-level message cannot name the module (`instProcess2` has no module
name in scope); `load_design_sv2`'s message does, and the runner reports the
kind (`run2: unsupported: unsupported process 'AlwaysComb:self-read'`).

**Justification** (`LeanModels/Sv/CombGuard2Sound.lean`): every admitted
body is idempotent on shaped states — one fuel induction over
`execStmt2`/`execCase2`/`execStmts2` (`CombGuard.sim`) relating the second
run's state to the first by `Inv M F τ σ` (every bit is the first run's, or,
outside the must-set, the final state's), with the first run's `Frame` as a
by-product:

    theorem runCombProcess2_alwaysComb_idem_of_admits {wd : String → Option Nat}
        {body : Stmt2} (hadm : body.combAdmits wd = true) {st r : SvState} {f : Nat}
        (hs : CombGuard.Shaped wd st)
        (h : runCombProcess2 f st (.alwaysComb body) = .ok r) :
        runCombProcess2 f r (.alwaysComb body) = .ok r

(and `CombGuard.execStmt2_idem_of_admits` at the statement level, any NBA
queue). So on an admitted body the settle loop's re-runs of the block are
the identity: the one run a simulator makes per wake-up already leaves the
block's settled value. It covers the FULL tier — blocking/nonblocking,
constant slices, run-time index reads and writes, procedural concatenation
targets, `if`, `case`/`case … inside` — not only the fragment `Comb2Proc`
lowers, and generalizes `runCombProcess2_alwaysComb_idem` from
`SymState.selfReadFree` (latches included). `#print axioms`: `[propext,
Classical.choice, Quot.sound]`, pinned with `#guard_msgs`.

**The guard and `selfReadFree` are different tests, neither stronger.** The
guard admits latches, which the lowering refuses; the lowering sees through
values that never reach an equation and accepts `y = t; y = a; t = b;` and
`if (t) y = a; else y = a; t = b;`, which the guard refuses (pinned:
`Comb2ProcExample.dead_lowers`/`dead_refused`, `same_lowers`/
`same_refused`). So "selfReadFree implies admitted" is FALSE in general;
what holds, and is checked: every body of `Comb2ProcExample` the lowering
accepts is admitted (`fa_admits`, `mux_admits`, `dec_admits` by `decide`,
`as_admits` for EVERY `N` by `simp` — each read the walk compares is on a
different signal than the bits written after it), every `agree.lean` design
with an `always_comb` instantiates to its hand-built twin unchanged, and a
scan of all 165 committed sv-0.2 envelopes at their defaults finds 62
`always_comb` processes of which exactly the 8 intended `rbw_*` fixtures are
refused. On a degenerate body of the second kind the API meets the guard's
loud process through `name.sem` (`lowerComb` is `none`), never a body the
guard let through.

**Fixtures and rows** (`Examples/system-verilog/sem2/`, all
`harness/sv/cases2.json`): `rbw_comb` and `rbw_held` are now refusal
fixtures — their `agree.lean` pins `load_design_sv2`'s refusal text with
`#guard_msgs` and checks (an `#eval` that throws on mismatch) that the
envelope instantiates to the hand-built design's declarations with
`combGuardProc` of its body as the only process; loud rows `rbw_comb`,
`rbw_held`, `rbw_bits`, `rbw_cond`, `rbw_case_item`, `rbw_dyn`, `rbw_part`,
`rbw_nested` (`AlwaysComb:self-read`) and `rbw_compound`
(`AssignmentExpression:compound`, refused upstream), each with its measured
Icarus/Xcelium trace and the settle answer in the row's `measured` field and
the table in `docs/sv-oracle-disagreements.md`; PASS rows `acg_latch_read`,
`acg_temp_all`, `acg_two_temps`, `acg_bits_ok`, `acg_part_ok`,
`acg_case_ok`, `acg_cond_ok`, `acg_dyn_ok`, `acg_nested_ok`. Verilator
5.042 and Yosys 0.53 (`prep; eval`, every two-state point) give the settle
answer on every refused shape; Icarus and Xcelium agree with each other
from cycle 1 on and disagree at cycle 0 (time-zero ordering). Xcelium 24.03
(one `refsim` run on `vip-ng`, one batched testbench) gave Icarus's trace —
hence the model's — on all 60 cycles of the ten admitted designs.

**Registry.** `sv-div-3` moved to `retired_rows` (`retired: 2026-10-28`,
`retired_by` recording that the written retirement condition — a `Sem2`
remodel — did NOT occur: the divergence is closed by making it unreachable
from ingested designs). Its guards stay and change meaning
(`harness/sv_divergence_probe.py`): `sv_div_3_still_divergent` now raises
the alarm when any refusal pin is gone (the `instProcess2` hook, an
`agree.lean` refusal pin or instantiation link, a `cases2.json` refusal row,
`rbw_guard`/`held_guard`) — checked to fire on a removed hook and on removed
`#guard_msgs` pins — and `sv_div_3_has_not_widened` keeps measuring the tool
split that justifies the refusal (hand-built `run2` pins = settle, Icarus =
the declared stale trace, Yosys = settle on 32/32 and 4/4 points).

**Gaps.** (1) The M0-tier family `name : Nat → … → Design`
(`PDesign.instantiateD`, `Param.lean`) of a `load_design_sv2` envelope also
fixpoint-settles `always_comb` and is NOT guarded (M0 paths untouched by
rule); at the defaults `load_design_sv2` refuses the whole envelope, so it is
reachable only at a non-default point of a parametric self-reading body.
(2) Cross-process bit splits are not self-reads and are not refused:
`always_comb t[0] = a;` (or `assign t[0] = a;`) next to
`always_comb begin t[1] = b; y = t; end` — Xcelium 24.03, Verilator and the
model re-run the second block when `t[0]` changes, Icarus 12 does not
(variable-granularity sensitivity, its own `sorry` warning); recorded in
`docs/sv-oracle-disagreements.md` as an Icarus departure, no row yet.
(3) Over-refusals, all loud: statically infeasible path combinations
(`if (c) t = a; y = t; if (c) t = b;`), dead reads and irrelevant
conditions (the two `selfReadFree`-accepted bodies above), and a run-time
index read of a partly written signal. (4) Hand-built `Design2` values
(`rbwDesign`, `heldDesign`) still run under `run2` with the settle answer;
the guard is applied at instantiation, not inside `Sem2` (unchanged).

**Measured.** `python3 harness/sv/diff_test2.py --sim iverilog` (after the
final build): 255 cases, 181 verified, 17 declared simulator disagreements,
23 unavailable backends (24 skipped), 33 loud refusals, 0 failed, 0 ERROR,
exit 0 (new: 9 verified `acg_*`, 9 loud `rbw_*`; `fa_comb_proc`,
`mux4_case`, `latch_comb`, `onehot_dec`, `addsub_comb*` keep PASS). Every
regenerable sv-0.2 envelope re-extracts byte-identically (161 same, 0 diff,
3 skipped: the cv32e40p sources are off-machine). The ∀-N proofs
(`ripple_add/{gen,proof,spec}`, `mul2d/gen`, `partsel/gen`, `ripple_fa/gen`),
every buildable `agree.lean` and `load_design_sv2` user, and
`LeanModels.Sv.{CombGuard2,CombGuard2Sound,Ingest2,Param,Param2,Gen2,Hier2,
Hier2Gen,Comb2Example,Comb2ConcatExample,Comb2Proc,Comb2ProcExample,Mono2,
SelfCheck}` build in one slot command with every existing statement
unchanged; `alu_div/ingest`, `ff_one/ingest` and `popcnt/ingest` import the
`LeanModels` umbrella and cannot build while the Python lane is red
upstream (not touched). `harness/sv_divergence_probe.py` PASS,
`harness/divergence_register.py` OK, `tools/docs_check.py` clean.

## The `always_comb` self-read guard: round-3 repairs (WP4) — 2026-10-28

Repairs after the independent verification of the entry above. No theorem
statement changed; nothing in `Sem2` changed.

**The justification theorem is now under the default build.** Nothing
imported `LeanModels.Sv.CombGuard2Sound`, so `lake build` never compiled
`runCombProcess2_alwaysComb_idem_of_admits` or its `#guard_msgs` axiom
pins. `Comb2ProcExample` now imports it and applies it (`latch_idem`: the
latch's one run is its own fixpoint, axioms pinned), and every
`Examples/system-verilog/sem2/*/agree.lean` that imports `Comb2ProcExample`
puts it under the `Examples` glob. The differential harness's olean list
(`SV_LEAN_MODULES`, `harness/sv/diff_test2.py`, Lane B's file) already
names `CombGuard2` in the working tree, so an edit of the guard can no
longer leave `runner2` on a stale `Param2.olean`.

**Icarus does not wake a block through an alias of a variable it writes.**
The guard is about ONE block re-run on its own result. A block that reads a
different variable aliasing one it writes is admitted, and there the LRM,
Xcelium and the model agree that the block wakes when the alias changes,
while Icarus 12.0 merges the alias with the written variable and keeps the
stale value. (CORRECTED round 4, Lane A, from the round-3 verifier's
measurements: Icarus does NOT merge the alias or drop it — its netlist keeps
it in the block's event list, `.event anyedge, w, a` / `.event anyedge, i,
a` — it propagates the copy's update synchronously inside the block's run,
so the wake-up is lost; IEEE 1800-2023 §4.7/§4.8 permit that interleaving,
so the two alias rows record a TOOL SPLIT, not an Icarus departure from
§9.2.2.2.1. The bit split, by contrast, IS a departure: Icarus leaves the
whole variable out of the list. `docs/sv-oracle-disagreements.md` has the
measured account.) Three admitted fixtures, each a `cases2.json` row with an
exact `oracle_disagreement` declaration (both traces pinned, source,
envelope, case and testbench hash-bound): `acg_alias_assign`
(`assign w = t; always_comb begin y = w; t = a; end`,
`iverilog-comb-assign-alias-sensitivity`), `acg_alias_port` (a child whose
input and output ports connect to one parent variable,
`iverilog-comb-port-loop-sensitivity`), `acg_xproc_bits`
(`always_comb t[0] = a;` beside `always_comb begin t[1] = b; y = t; end`,
`iverilog-comb-bit-split-sensitivity`). One batched Xcelium 24.03 run
(fleet gate `refsim` on `vip-ng`) gives the model's trace on all 23 cycles
of the three rows, `x` included; Verilator 5.042 gives it with `x` read as
0. Icarus alone also merges `wire [1:0] w = t;` and `assign t[0] = a;` the
same way, and does not merge `assign w = ~t;`. Traces:
`docs/sv-oracle-disagreements.md` ("Icarus does not wake a block through an
alias…"; retitled in round 4 "Icarus propagates a copy inside the block's
own run" and "Icarus leaves a partly written variable out of the
sensitivity list"). The claim "across blocks both readings re-run a block" is
qualified accordingly in the `CombGuard2Sound.lean` and `Comb2Proc.lean`
docstrings and the schema doc. CORRECTION to gap (2) of the entry above:
Icarus prints NO diagnostic on the bit split; its `sorry: constant selects
in always_* processes` warning appears only when a block READS a constant
select (`rbw_bits`, `rbw_part`, `rbw_child`, `acg_bits_ok`).

**The bit split is outside the standard.** IEEE 1800-2023 §9.2.2.2: the
variables an `always_comb` writes "shall not be written to by any other
processes" — variable granularity. (CORRECTED round 4, Lane A: the 2023
text continues "However, multiple assignments made to independent elements
of a variable are allowed as long as their longest static prefixes do not
overlap", and §6.5 makes each bit of a packed type an independent element:
the bit split is LEGAL, bit-granular exactly like `procExclusiveOk`, and a
variable-granular refusal would be an over-refusal. The row's declaration no
longer names that exit.) ls-sv's one-driver rule
(`procExclusiveOk`) is bit-granular and admits `acg_xproc_bits`, as do
Xcelium and Verilator. The row cites §9.2.2.2 and its retirement condition
names both exits (Icarus re-runs the block, or ls-sv refuses
variable-granular multi-writers). Refusing them is NOT done here: it is a
design-level rule, and composing one beside `Design2.driverGuard` would
falsify the pinned statements listed in the entry above (`driversOk_iff`
and the `…_of_ok` family). Recorded as an open gap.

**A child's refusal names its instance.** The guard runs on the child's own
instantiation, where neither the instance nor the flattened names are known.
`instBodyProc` (`Hier2.lean`) now passes every flattened child process
through `Process2.inInstance pfx i`, which leaves every process unchanged
except an `AlwaysComb:self-read` refusal, whose message gains the clause
`in instance '<inst>' of module '<child>' (its signals flatten under the
prefix '<path>'):` — one clause per level, outermost first. (Round 4: the
clause now reads `… under the prefix '<prefix>' inside the module that
instantiates it`, because each level's prefix is relative to its parent —
the round-3 verifier's `n_nest` read as if the leaf's signals were under
`l.` where they are under `m.l.`.) `Process2.inInstance`
is a `@[simp]` definition with one equation per constructor, so the
concrete flattening proofs (`ripple_fa/gen.lean`'s `fa_flatten`) go through
unchanged. Fixture `sem2/rbw_child` (`t[0] = a; y = t[1]; t[1] = b;` in the
instance `u` of `rbw_child_leaf`): its `agree.lean` pins
`load_design_sv2`'s refusal text ("in the instantiated design of module
'rbw_child': in instance 'u' of module 'rbw_child_leaf' (its signals flatten
under the prefix 'u.'): always_comb block reads bit [1] of 't' …") and
checks that the flattened design's only loud process is exactly that
refusal and that the child's `t` is `u.t`; loud row `rbw_child` (Icarus
12.0 y = 0 0 1 1 0, settle y = 0 1 1 0 0). A FLAT top's process message
still names no module: the `Design2` that carries it is the module, and
`load_design_sv2` names it; `runner2` prints only the kind (Lane B's file,
not edited).

**Measured.**
`python3 harness/sv/diff_test2.py --sim iverilog`, one clean full run
after the final build: 271 cases, 189 verified, 20 declared simulator
disagreements (3 new: the alias rows), 23 unavailable backends (24
skipped), 38 loud refusals (new: `rbw_child`), 0 failed, 0 ERROR, exit 0;
multi-point cross-check 111 row points agree, 4 unconfirmed but
simulator-verified. (An earlier full run had 3 ERROR rows,
`case_width_n1/n32/n33`, with "object file … Probe2.olean / Ingest2.olean
does not exist": the other lane's concurrent `diff_test2` rebuilt those
oleans mid-run; the three passed when rerun, and the clean run above has
none.) Every regenerable sv-0.2 envelope re-extracts byte-identically (173
same, 0 diff, 3 skipped: cv32e40p sources off-machine). One slot build of
`LeanModels.Sv.{CombGuard2,CombGuard2Sound,Param,Param2,Hier2,Hier2Gen,
Probe2,Ingest2,Gen2,Comb2Example,Comb2ConcatExample,Comb2Proc,
Comb2ProcExample,Mono2,SelfCheck}`, the ∀-N proofs (`ripple_add/{gen,proof,
spec}`, `mul2d/gen`, `partsel/gen`, `ripple_fa/gen`) and every buildable
`agree.lean`/`load_design_sv2` user (now including `sem2/rbw_child`) is
green with every existing statement unchanged.
`harness/sv/test_oracle_disagreements.py` OK, `harness/sv_divergence_probe.py`
PASS, `harness/divergence_register.py` OK, `tools/docs_check.py` clean.

**Gaps, updated.** (1) The M0 family (`PDesign.instantiateD`) of a
`load_design_sv2` envelope is still unguarded (unchanged). (2) Variable-
granular multi-writers of an `always_comb` variable (§9.2.2.2) are admitted
(row `acg_xproc_bits`, declared). (Round 4: they are LEGAL in IEEE
1800-2023 — independent elements; the open item is Icarus's departure, a
class wider than the row: `x_dyn`, `x_child`, `assign t[0] = a;`.) (3) The over-refusals of the entry above
are unchanged. (Round 4, Lane A: one more, documented in the rule text but
missing here — a procedural concatenation target must-writes nothing,
`Lhs2.mustW .concat => []`, so `{t, u} = a; y = t; t = b;` is refused as a
self-read although every tool treats `t` as written before the read; the
soundness proof already covers concatenation targets, so a must-write of
their ident/constant-slice leaves is the fix.) (4) A flat top's process message names no module (the
design is the module); `runner2` prints only the refusal kind.

## Default-point folds, round 3 (WP FOLDS, Lane B) — 2026-10-28

The CX cross-check made the default-point fold class loud at probed points;
this package removes the five folds the round-2 gap list still carried (and
the CX verifier's non-ANSI initializer), so each is exact or loud at EVERY
point, not only where a probe looks — in VALUE positions; the verifier then
found items 1 and 2 still silent in symbolic positions (case items, select
labels) and in the constant tier's typed localparams, fixed in the repair
round below; the next verifier found that repair's root-context floor
wrong (silent values in self-determined roots, `integer`/`int` targets and
genvar initializers), fixed in "Default-point folds, round 4" below.
`docs/sv-envelope-schema.md`,
"Default-point folds, round 3", is the reference; rows `fold_*` and
`pi_nonansi*` in `harness/sv/cases2.json`.

1. **Signed simple operands in an unsigned context** (repros `ib_pneg`,
   `ib_neg32`, `sp`). The extractor dropped every same-width conversion,
   so `a + P` (`int P = -3`) carried a bare `ParamRef` that Lean
   SIGN-extended wherever the context outgrew 32 bits; §11.8.2 zero-extends
   a simple operand converted to an unsigned type, and Icarus 12.0 and
   Yosys 0.53 agree. In a parametric family the conversion is now kept as
   `Resize(width, operand)` for a signed `ParamRef`/`GenvarRef`/`$high`/
   `$size` (`_sym_unsigned_simple_operand`); the widening twin (previously
   `ConversionExpression:width`) is the same node. Lean lowers it as
   materialization at or below its width and zero extension above
   (`instExpr2`), folds constant subexpressions at the operation width
   (`constAtCtx2`), and the constant tier's `resize` reduces a signed
   operand modulo its own width first (`evalAt`/`evalInt`). A NEGATIVE
   genvar in that position splits the oracles (Icarus sign-extends,
   Yosys/Verilator zero-extend): refused, `GenvarRef:unsigned-extension`.
2. **A default-point truncation of a context-propagating operator** (repro
   `sx`): `c = a + b` truncated at `N = 2` kept the 4-bit sum at `N = 8`.
   `instExpr2` now lowers a `Resize` around `+ - * / % & | ^ ~ - ?:` and
   shift/power left operands at a WIDER context (`PExpr.ctxPropagates`).
3. **Selects of a parameter's value** (repro `ps_param`): the extractor
   keeps the legacy encoding only over a range canonical at the default
   point (raw labels) or with literal bounds (folded offsets, not an
   indexed part select) and refuses everything else (`<kind>:param-range`,
   which also caught a wrong-at-every-point `R[0 +: 2]` over a literal
   `[0:3]`); Lean checks the canonical range at each point (`IEnv.pdims`,
   `paramSelectOk`).
4. **Genvar and run-time labels** (repro `vb3`): the legacy-select range
   guard (`LeanModels/Sv/RangeGuard2.lean`, `PDesign.legacyRangeReport`)
   refuses a point where a legacy-selected declaration the instantiated
   design still mentions has a range other than literal bounds or `[m:0]`,
   `m ≥ 0` (`Select:legacy-range`), every module at its own point. It is a
   check BESIDE `name.sem` (load gate at the defaults and every probed
   point, `probeCheckString`, the differential runner) — DEVIATION from the
   preferred "in the guard composition": every place `name.sem` composes is
   pinned by a recorded statement (`instExpr2_bitSel_ident_dyn`,
   `instantiate2_eq`, `instantiateG2_of_ok`, `instantiateGD2_of_ok`,
   `instantiateH_of_rec`, `instantiateH_flat`, the ∀-N examples'
   `ripple_paramEnv`/`ripple_elems` stated for every `N : Int`, and the
   svGolf reference solutions' `show …instantiateGD2…`), so any guard there
   falsifies an existing statement. Only REACHED selects count, so
   `ripple_add` passes at `N = 0` (its loop has no iteration).
5. **`$high`/`$size`** read the declaration's first packed dimension at
   each point (`dimQuery`), loud without one; value positions admit them
   (Icarus 12.0 cannot evaluate them in generate conditions). Found while
   testing them: `$left`/`$right`/`$low` in a value position were a silent
   fold — the tier refused the call and the conversion around it fell back
   to slang's DEFAULT-point constant (`$left(v)` read 2 at every `N`). A
   conversion whose operand converted to `Unsupported` and names a symbol
   is no longer folded in a parametric family
   (`ConversionExpression:default-point-fold`), except a query of a range
   with literal bounds.
6. **Non-ANSI output-port initializers** (CX verifier major): `convert_port_sym`
   reads the internal variable's initializer when the port symbol has none.
   Minors: `_sym_initialized_target` fails closed (`…:initialized-unknown`)
   and runs once per site; schema wording fixed.

The cross-check gains normalization rule 6 (`Probe2.lean`): `resize w (a op
b)` for `+ - *` distributes when no operand bit above `w` can be x/z (the
envelope's `a + B` at a 4-bit point against slang's `resize 4 (resize 8 a +
8'hfd)`).

**Measured.** 50 new rows over 13 new fixtures (`sem2/fold_pneg`,
`fold_sparam`, `fold_pgen`, `fold_ctxres`, `fold_psel`, `fold_vsel`,
`fold_query`, `fold_lrq`, `fold_lrq_fixed`, `pi_nonansi`, `pi_nonansi_reg`,
`pi_nonansi_hier`, `pi_nonansi_p`): 43 PASS against Icarus 12.0 at points
including N = 0, -1, 1 and widths across 32 (N = 30, 31, 40), every one with
the cross-check agreeing at its point (31 row points); 7 loud refusal rows
(`fold_psel_n1`, `fold_psel_n0`, `fold_psel_nm1`, `fold_vsel_n0`,
`fold_vsel_nm1`, `fold_pgen_n40`, `fold_lrq`). Yosys 0.53 (`chparam; synth -flatten; abc`, the netlist
simulated in Icarus with the row's testbench) agrees with every passing row
on every cycle whose inputs are all 0/1, except `fold_vsel_n1`'s
out-of-range reads, which the model and Icarus read as x and the netlist
resolves (x is a synthesis don't-care). Before the fixes the model failed
`fold_pneg_n31/n40*` (sign extension of `P`), the `fold_ctxres` points above
4 bits, the cross-check at `fold_sparam_n3`, and read `fold_psel`/`fold_vsel`
at N ≤ 0 silently. The CX sweep rerun over every probed envelope (76,
1305 entries): every one of CX's 1165 entries keeps its verdict; of the 140
new ones 135 agree and the 5 failing are exactly the refused points of
`fold_psel` and `fold_vsel` (the cross-check itself reports `fold_vsel` at
N = 0 as a silent fold). Full `python3 harness/sv/diff_test2.py --sim
iverilog` on the final tree: 321 cases, 232 verified, 20 declared simulator
disagreements, 24 skipped (23 unavailable Icarus backends), 45 loud
refusals, 0 failed, 0 ERROR, exit 0; cross-check 142 row points agree, 4
unconfirmed but simulator-verified.
Every regenerable sv-0.2 envelope re-extracts byte-identically (186 same,
0 diff, 3 cv32e40p skipped); the two that changed — `partsel` (the
run-time base `sel*W` now carries `Resize(32, W)`: the same Design2 at every
point, its `#guard`s unchanged) and `sem2/register_file_ff` (`waddr == gidx`)
— were regenerated, with `partsel.sv.probes.json`. Extractor suite 1763
passed, 3 skipped (`PYTHONHASHSEED` 1 and 2; new `test_sym_folds3.py`;
`test_symbolic_default_point`'s widened-parameter test updated: loud before,
a `Resize` now). One slot build of the SV modules
(`RangeGuard2` new), the ∀-N proofs, every buildable `agree.lean` and
`load_design_sv2`/`instExpr2` user (75 jobs) is green with every existing
statement unchanged; the three umbrella-importing cv32e40p `ingest.lean`
files elaborate cleanly with the `import LeanModels` line removed (scratch
copies). `docs_check` clean, `divergence_register` OK.

**Gaps.** (1) The range guard is not in `name.sem` (above): a proof about
`name.sem` at a point no consumer checks — not a load default, not a probed
point, not a row — still sees the legacy offset reading there. (2) A
`Resize` around a context-propagating operator is propagated only into a
WIDER context; whether slang ever emits such a `Resize` for a widening (not
a truncation) at the default point is argued, not measured exhaustively.
(3) `$left`/`$right`/`$low` stay outside the tier; `$high`/`$size` in a
dimension bound of a LATER declaration are loud during the geometry pass
(`dimTable` threads widths, not ranges). (4) An initializer needing a width
or sign conversion is still loud (Ports and Vars). (5) The extractor
test `test_empty_associative_delete::test_symbolic_mode_stays_loud` is
flaky under some `PYTHONHASHSEED` values (seeds 1 and 5 fail) with the
HEAD extractor too — pre-existing, not investigated.

### FOLDS repair round (verifier round 3, Lane B) — 2026-10-28

The verifier found items 1 and 2 above exact only in VALUE positions. Both
majors are fixed; `docs/sv-envelope-schema.md`, "Default-point folds in
symbolic positions and constant contexts (round 3 repair)", is the
reference.

1. **Symbolic positions** (major, repros `vp_case`, `vp_case2`, `vp_idx`).
   `case (a) P:` and `v[a - P]` (`int P = -3`, `a` 42 bits at `N = 40`) read
   a bare `ParamRef` that Lean sign-extended: `_sym_unsigned_simple_operand`
   returned None under `_SymPos`. In a parametric family the symbolic
   positions now carry the value-position conversions: the marker (and its
   widening twin, formerly `ConversionExpression:width`), `Resize(w,
   literal)` for a widened sized literal and `SignedResize`/`Resize` for a
   sized signed one (`_sym_literal_widening`, `_sym_signed_literal_conversion`),
   and a signed reference-free constant under an assignment-like width
   change keeps its tree under a conversion of the target width
   (`_sym_signed_constant_symctx`; any other such conversion is
   `ConversionExpression:signed-constant`, as in value positions). Hunting
   with them: a literal folded at the default context also inflated widths
   where the context is NARROWER (`v[s + 1'b1]` indexed at 4 bits at `N = 2`,
   case items `2'b11 + 2'b01` compared at 4 bits), and `localparam logic
   [N-1:0] L = 300` / `= -1` / `= 8'sd100` were folded at the default width.
2. **The constant tier** (major, repros `vp_lp2`, `vp_lp`). `evalAt`/`ctype`
   read every `Resize` width as the context, but it is the DEFAULT point's:
   `localparam logic [N-1:0] L1 = 8'd200 + 8'd100` was 12 at every `N`.
   `ctype` is now transparent to `Resize`/`SignedResize` (a `Squash2` keeps
   its width as a floor), `evalAt` evaluates a context-propagating operand
   (`PExpr.ctxPropagates`, moved from Param2) at the context it is handed
   and never truncates to the envelope's width, and a root's context is
   supplied: a typed localparam or typed parameter default at its declared
   width HERE (`evalAssign`, `PParam.evalDefault`); a self-determined root
   (label, generate condition) at its own width here (`rootType`), which
   also fixes `U > 5` at a 40-bit `U` (truncated to the default 32 before)
   and `U + 8'd200 < 8'd50` at a narrower `U`; and a root whose target was
   pushed into every operand (a genvar initializer, an `int` localparam, an
   INT-class override) keeps the conversions' width as a floor
   (`PExpr.chainInfo`). [Round 4 correction: this floor was wrong — it read
   the signed-operand marker and widened literals, which carry the default
   point's widest-operand width, as a pushed target, giving self-determined
   roots that width (`v[SB + 1'b1]`), missed `integer`/`int` targets with no
   conversion to read, and followed Icarus on genvar initializers where the
   oracles split. Replaced; see "Default-point folds, round 4" below.] `constAtCtx2` evaluates at `max(context, own
   width)` in every case. A negative genvar zero-extended past 32 bits is
   loud in the constant tier too (`PExpr.negGenvarAt`).
3. **Found while measuring with Yosys 0.53 and Verilator 5.042** (no
   Xcelium this round, per the user):
   (a) a TYPED instance override that is a context-propagating expression
   (`.P(U + 8'd100)` into `logic [15:0] P`) splits the tools — §10.8 and
   Icarus evaluate it at the parameter's width (300), Yosys and Verilator
   at its own (44) — and the constant tier evaluates an override without
   the child's type: refused, `InstanceSymbol:override-context`
   (`_sym_override_root`); recorded under "Refused where the oracles split"
   (4). By the old rules the model followed Icarus there, silently.
   (b) Yosys evaluates a plain `case` item at its own width (`2'b11 +
   2'b01` is 0, not 4 in a 4-bit case); the model, Icarus and Verilator
   follow §12.5 — recorded as synthesis-side divergence 3.
   (c) A run-time select index wider than 32 bits whose value is out of
   range: Icarus 12.0 (and Verilator) read the bit at its low 32 bits, the
   model and Yosys `prep; eval` read x (§11.5.1) — declared Icarus
   disagreement `iverilog-wide-index-truncation`, row `fold_pcase_wide`.
   Not refused like the wide part-select base: the refusal would sit in
   `instExpr2`'s select arm, whose lemmas are stated for every environment.
4. **Minors.** The round-3 entry above and the schema section now say
   "value positions"; `_sym_unsigned_simple_operand`'s docstring covers the
   symbolic positions. The range guard's two compromises stay documented
   (Gaps 1 above).

**Measured.** 34 new rows over 7 new fixtures (`sem2/fold_pcase`,
`fold_lpgrow`, `fold_lpshr`, `fold_cgrow`, `fold_lshr`, `fold_ovr`,
`fold_ovr2`): 32 PASS against Icarus 12.0 with the cross-check agreeing at
every row point (`fold_pcase*` N = 7, 31, 40, P = -3, -1, 5;
`fold_lpgrow*` N = 2, 3, 4, 8, 16, 31, 40; `fold_lpshr*` N = 4, 8, 9, 12,
16, 40; `fold_cgrow*` N = 4, 8, 32, 33, 40; `fold_lshr*` N = 1, 2, 3, 4,
5; `fold_ovr2*` N = 4, 8, 16, 20), one declared Icarus disagreement
(`fold_pcase_wide`), one refusal row (`fold_ovr`). The verifier's own
repros (`vp_case`, `vp_case2`, `vp_idx`, `vp_lp`, `vp_lp2` at the points
they named, N = 31/40, P = -1) PASS, except `vp_idx`'s out-of-range wide
indices (3c). The verifier measured the old model failing `vp_case`,
`vp_case2` and `vp_idx` at N = 40 and `vp_lp2`/`vp_lp`; for the new
fixtures the old reading follows from the old rules (literal and `Resize`
widths of the default point) and was not re-run. Yosys 0.53 (`synth -flatten;
abc`, the netlist simulated in Icarus with each row's testbench) agrees on
every known-input cycle of `fold_lpgrow*`, `fold_lpshr*`, `fold_cgrow*`,
`fold_ovr2*`, `fold_lshr_n1`/`_n2` and of the six regenerated envelopes'
rows except `case_width_n33`/`_n40` (3b); `fold_pcase*` differ only on
out-of-range reads (x in the RTL, a don't-care in the netlist), `fold_lshr`
at N = 3, 4, 5 on the case items (3b). Verilator 5.042 matches Icarus on
`fold_lpgrow`, `fold_lpshr`, `fold_cgrow`, `fold_lshr` and `fold_ovr2`;
on `fold_pcase` at N = 40 it SIGN-extends the bare case item `P:` (Icarus,
Yosys and §11.8.2 zero-extend). Extra hunting repros (scratch): generate
conditions `P < U`, `U - P > 33'h1_0000_0000`, `(U + 8'd200) >> 8` at N =
4, 8, 33, 40 and P = 5, a genvar compare against `B + 4'd1` at N = 1, 2, 8,
and a run-time base `v[s - P -: 4]` at N = 2, 4, 30 PASS (at N = 40 the
wide-base refusal). Full `python3 harness/sv/diff_test2.py --sim iverilog`:
355 cases, 264 verified, 21 declared simulator disagreements, 24 skipped
(23 unavailable Icarus backends), 46 loud refusals, 0 failed, 0 ERROR, exit
0; cross-check 171 row points agree, 2 unconfirmed but simulator-verified
(pre-existing). CX sweep (85 envelopes, 1463 entries): every one of the
previous 1305 entries keeps its verdict except `case_width` at N = 33 and
40, UNCONFIRMED → ok (the widening twin now extracts at the point); of the
158 new entries 145 agree and 13 are loud refusals (`fold_ovr` at every
point, `fold_ovr2`'s constant part select out of range at N ≤ 3). reext:
193 same, 0 diff (3 cv32e40p skipped) after regenerating the six envelopes
the symbolic-position conversions change — `sem2/aggregate_param`,
`case_width`, `fold_psel`, `fold_sparam`, `int_const_flat`, `param_types`
(same values at their rows' points; their rows keep their verdicts).
Extractor suite 1775 passed, 3 skipped (`PYTHONHASHSEED` 1, 2, 3, 5; new
`test_sym_folds3r.py`; `test_symbolic_param_widths`' widened-parameter
label test updated: loud before, the zero-extension marker now). One slot
build of the SV modules, the ∀-N proofs, every buildable `agree.lean` and
`load_design_sv2` user is green with every statement unchanged; new
`#guard`s in `Param.lean` pin `evalAssign`, `rootType` and the
negative-genvar refusal. `docs_check` clean, `divergence_register` OK.

**Gaps.** (1) A typed override of a context-propagating expression is
refused, not modelled (the tools split). (2) A genvar initializer or
`int` localparam whose pushed-down target is out of reach keeps the default
point's width as its floor — exact for a fixed target (`int`, a genvar),
which is every such target in the tier; a typed localparam goes through
`evalAssign`. [Round 4 correction: FALSE as written — the verifier's
`rf_int`/`rf_ipar` (an `integer` target read at its operand's own width) and
`rf_gv` (a genvar initializer, where Icarus and slang/Yosys split) were
silent wrong values; repaired in "Default-point folds, round 4" below.] (3) The wide-index Icarus disagreement is declared, not
refused. (4) svGolf (a separate lake project) was not rebuilt or re-checked
here. (5) The range guard stays a check beside `name.sem` with name-level
reachability (verifier minor, no change).

## Declaration initializers, every form, and the always_comb/always_ff mixture (round 4, Lane A) — 2026-10-28

The open round-3 initializer and documentation majors (CX verifier: the
non-ANSI port initializer, the fail-open target walk, the width-converted
initializer; WP4 verifier: `vg_initc` rejected by Xcelium, the alias
declarations' mechanism and LRM position) and the minors. Extractor changes
are symbolic-only and additive (`convert_port_sym`, `convert_var_sym`, the
initialized-target walk, one `_SYM`-gated hook in
`convert_procedural_block`); `Hier2.lean` changes one message string; no
theorem statement changed and no M0 path was touched.

**(1) Every output-port initializer form.** The round 3 folds already read
the internal variable's initializer for the separate non-ANSI declaration
(`output [1:0] y; logic [1:0] y = 2'b10;`). Round 4 enumerated every form
slang accepts — ANSI `logic`/`reg`/`var logic` (port symbol), ANSI shared
declarations and packed structs (port symbol), non-ANSI separate
`logic`/`reg`/`var logic` and scalars (internal variable), non-ANSI single
`output reg`/`logic`/`var logic … = …;` and shared ones (port symbol) — and
pins each (rows `pi_ansi_forms`, `pi_ansi_multi`, `pi_nonansi_forms`,
`pi_hier_plain`; `test_sym_initializers.py` for the non-ANSI `output var
logic` single declaration, which Icarus 12.0 does not parse). It found one
more SILENT WRONG: a non-ANSI port with an explicit port expression
(`module m(clk, a, .q(y))`, or `module m(y[1:0])`) was emitted as a `Port`
`q` and an unconnected `Var` `y`, so `q` read its initializer (`10`)
forever where Icarus 12.0 gives `11, 10, 1x`; it is now
`PortSymbol:explicit-expression` (row `pi_explicit`; Xcelium 24.03
elaborates it, Verilator 5.042 and Yosys 0.53 do not parse it). The
width-converted literal initializer (`output logic [3:0] y = 2'b10`,
slang's `Resize`/`SignedResize`), refused before as "non-literal
initializer", is now lowered exactly (`_sym_decl_init`): a 0/1 literal to
the `Int` of its value, which `instDecl` converts at each point's declared
width (`LVec.ofInt` — zero-/sign-extension and truncation exactly, also in a
parametric family whose conversion width is the default point's), an x/z
literal to the `Literal` of a declared width that is fixed at every point
[CORRECTED, round 4 repair below: not exact — an UNSIZED x/z literal was
padded with 0, and a literal with NO conversion at the default point was
still stored at the default width at every point];
everything else stays loud (an x/z literal at a parameter-dependent width,
row `pi_width_px`; an x/z sign bit; a negated literal). Rows
`pi_width_forms`, `pi_width_p` and `pi_width_p_n1/_n2/_n8/_n40`
(`xcheck:agree`) and `pi_hier_plain` (a child at `W = 5`).

**(2) The initialized-target walk fails closed.** `_sym_initialized_target`
returned `None` — admitted — for an expression shape it did not know, and
its port lookup swallowed exceptions; both now give `"unknown"`
(`_sym_initialized_target_info`), refused as
`ContinuousAssignSymbol:initialized-unknown` /
`PortConnection:initialized-unknown` with the construct named in `text`.
No existing envelope changed.

**(3) A declaration initializer counts as a writer of an `always_comb` /
`always_ff` variable — refused.** IEEE 1800-2023 §9.2.2.2/§9.2.2.4 let no
other process assign such a variable; §6.5 counts "a declared variable
initialization" as a procedural assignment, §10.5 calls it "a special case
of procedural assignment", §4.2 lists procedural assignment statements
among processes — no clause decides outright. Measured: Xcelium 24.03
rejects 41 of 41 probes (`xmelab: *E,MULAXX: Multiple drivers to
always_comb/always_ff output variable`): `always_comb` AND `always_ff`, bit
and whole-variable writes, every port form, flat and in a child; Verilator
5.042 stops on `MULTIDRIVEN` for a whole-variable `always_comb` write;
slang accepts all of them, Icarus 12.0 and Yosys 0.53 every one they parse
and do not reject for an unrelated reason (one and four probes). The tools split on
legality, so the block is refused
(`ProceduralBlockSymbol:initialized-variable`, `_sym_proc_initialized_write`:
every assignment and increment target of the body, block-local and
automatic variables excluded, fails closed). A plain `always` writer is
unrestricted (§9.2.2.1) and Xcelium runs it: admitted. Rows CORRECTED from
PASS to loud (this round's own rows, the claim "a declaration initializer
plus an always_comb writer is legal" withdrawn): `vg_initc`, `vg_initq`,
`vg_initqp`, `vg_initqp_n1/_n3/_n5`, `pi_nonansi`, `pi_nonansi_hier`,
`pi_nonansi_p`, `pi_nonansi_p_n1/_n2/_n5`; new loud rows `vg_initf` (flat
`always_ff`) and `vh_initcomb` (a child's `always_comb`). Before: `vg_initc`
PASS against Icarus (y = 11, 10, 1x, 1z) while Xcelium refuses to elaborate
it; after: refused, kind in the envelope. The round-2 item "Hier2's §6.5
mixture clause misses declaration initializers" is closed by the round-3
extractor guard in flat designs (`vg_init`, `vg_initp`) and hierarchical
ones [CORRECTED, round 4 repair below: not for a non-ANSI INPUT whose
separately declared variable has an initializer, which the `Port` dropped
— now `PortSymbol:initialized-input`] — a parent variable driven by an instance output (`vh_init`) and,
new, a child's own `assign` to its initialized output port (`vh_initp`:
Icarus "Unable to assign to unresolved wires", Xcelium `*E,ICDDIV`, Yosys a
conflicting constant driver).

**(4) The alias and bit-split declarations, rewritten from measurements.**
Round 3 said Icarus 12 "merges the pure alias with `t` and drops it from the
sensitivity list" and filed `acg_alias_assign`/`acg_alias_port` as Icarus
departures from §9.2.2.2.1. Measured instead (`iverilog -g2012` netlists of
the committed sources): the copy IS in the block's event list (`.event
anyedge, w, a`; `.event anyedge, i, a`); Icarus propagates the copy's
update synchronously inside the block's run, before the block reaches its
event control, so the wake-up is lost (probe `mech_buf`: `y = 00, z = 01`
at `a = 01` — the read after the write already sees the new copy; a `NOT`
copy is scheduled and agrees). §4.7/§4.8 permit that interleaving ("the
simulator is correct in displaying either"), so the two rows record an
LRM-PERMITTED TOOL SPLIT; Xcelium 24.03, Verilator 5.042 and Yosys 0.53
(`eval`, re-measured) give the model's answer. By the refuse-where-the-tools-split
policy they are refusal candidates; the refusal (an `always_comb` reading a
continuous copy of a variable it writes, through `assign` chains or a port
loop that forms only after flattening) is not built — it cannot enter
`name.sem` without falsifying `PDesign.instantiateGD2_eq_driverGuard` /
`Design2.driverGuard_of_ok`, and would sit beside it like the range guard —
so the declarations stay, re-worded: reference §4.7/§4.8, the measured
mechanism, a retirement condition that does not hold today. The bit split
(`acg_xproc_bits`) is the opposite case: LEGAL in 2023 (§9.2.2.2 "multiple
assignments made to independent elements of a variable are allowed";
§6.5: each bit of a packed type is one), so round 3's "outside the
standard at variable granularity" is withdrawn, and Icarus DOES depart from
§9.2.2.2.1 (its netlist leaves all of `t` out: `.event anyedge, b`). The
class is wider than the row: `x_dyn` (`y = t[s]`) and `x_child` (a child
port drives `t[0]`), both admitted, both stale in Icarus only (event lists
re-checked). Fixture headers, the three declarations (source and envelope
hashes rebound after the header edits; case, testbench and traces
unchanged), `docs/sv-oracle-disagreements.md`, the schema's self-read
paragraph, the `CombGuard2Sound.lean`/`Comb2Proc.lean` docstrings and the
round-3 WP4 charter entries (in-place CORRECTED notes) now say this.

**(5) Minors.** `Process2.inInstance`'s clause now reads "its signals
flatten under the prefix '<p>' inside the module that instantiates it"
(each prefix relative to its own level, so a nested leaf's names are the
concatenation; `rbw_child/agree.lean`'s pin updated); the `Lhs2.mustW
.concat => []` over-refusal is in the WP4 gap list; the schema's sidecar
pointer already read "above" (fixed in the round 3 folds).

**Before → after (oracle traces).** `pi_explicit`: Icarus 12.0 `q = 11, 10,
1x`; the model before the change kept `q` at its initializer (`10`, the
`Port` and an unconnected `Var y`), after it refuses
(`PortSymbol:explicit-expression`). `pi_width_forms`/`pi_width_p_n8`: before
`decl …: non-literal initializer outside the M0 tier` (loud), after PASS
(`w1 … w8 = 1010 10 1110 0010 0110 0…011 01x1 1001` at cycle 0; at `N = 8`
`y = 00000011, z = 11111110, u = 0000000101`), Icarus 12.0 = Xcelium 24.03
on every cycle of every new admitted row (row testbenches from
`gen_tb2`, run under both). `vg_initc`/`vg_initf`: before PASS against Icarus
(`y = 11, 10, 1x, 1z` / `11, 10, 1x`), Xcelium refuses to elaborate them;
after refused (`ProceduralBlockSymbol:initialized-variable`).

**Measured.** Extractor suite from the repo root: 1793 passed, 3 skipped, 1
failed — `test_empty_associative_delete::test_symbolic_mode_stays_loud`,
flaky at HEAD too (2 of 8 HEAD runs fail; unrelated). `test_sym_initializers.py`
26 tests (15 new). Re-extraction: 211 same, 0 diff, 3 skipped (cv32e40p
sources off-machine; their committed envelopes carry no initializer); the
envelopes this change alters were regenerated — `vg_initc`, `vg_initq`,
`vg_initqp`, `pi_nonansi`, `pi_nonansi_hier`, `pi_nonansi_p` (the block
becomes `Unsupported`) and `acg_alias_assign`, `acg_alias_port`,
`acg_xproc_bits` (header comments; their declarations' source and envelope
hashes rebound) — and before the edits a first sweep showed exactly the six
process-level differences and nothing else. svGolf's 22 reference and
scoring sources extract byte-identically with and without this round's
changes. One slot build of `LeanModels.Sv.{Ingest2,Probe2,Param,Param2,
RangeGuard2,Gen2,Hier2,Hier2Gen,CombGuard2,CombGuard2Sound,Comb2Example,
Comb2ConcatExample,Comb2Proc,Comb2ProcExample,Mono2,SelfCheck}`, the ∀-N
proofs (`ripple_add/{gen,proof,spec}`, `mul2d/gen`, `partsel/gen`,
`ripple_fa/gen`), the `load_design_sv2` proof users (`division`,
`implication`, `multiplication` + spec, `power`, `remainder`, `shifts`,
`wildcard_equality`) and all nine sem2 `agree.lean` files: 70 jobs, green,
every `#print axioms` (26) within `[propext, Classical.choice, Quot.sound]`.
`test_oracle_disagreements.py` OK, `sv_divergence_probe.py` PASS,
`divergence_register.py` OK, `docs_check.py` clean.
`python3 harness/sv/diff_test2.py --sim iverilog` (one run under the slot,
370 cases at its start): 258 verified, 21 declared simulator
disagreements, 24 skipped (23 unavailable Icarus backends), 63 loud
refusals, 0 FAIL, 0 ERROR — and 4 `XCHECK-FAIL`, all Lane B's
`fold_pneg_n31`, `fold_pneg_n31_pm1`, `fold_pneg_n40`, `fold_pneg_n40_pm1`
(`a + P * 2` folded in the default envelope's instantiation but a `mul` at
the point), which Lane B's own concurrent full run reproduces while it edits
`Param.lean`; this lane's extractor leaves `fold_pneg`'s envelope and its
`N = 31` sidecar byte-identical (checked with and without the round-4
changes). Every row of this entry: `pi_ansi_forms`, `pi_ansi_multi`,
`pi_nonansi_forms`, `pi_nonansi_reg`, `pi_width_forms`, `pi_width_p`,
`pi_width_p_n1/_n2/_n8/_n40` (`xcheck:agree`), `pi_hier_plain` PASS;
`pi_width_px`, `pi_explicit`, `vg_initf`, `vh_initcomb`, `vh_initp` and the
twelve corrected rows loud with their kinds; the three re-worded
declarations CHECKED (their rebound hashes and unchanged traces accepted).

**Gaps.** (1) The alias rows stay DECLARED although the policy says refuse
where the tools split: the refusal needs a cross-process alias analysis
beside `name.sem` (load gate and runner), not built here — a lead decision.
*(Closed 2026-10-29, round 6, lane B: the alias guard `AlwaysComb:alias-read`
(`LeanModels/Sv/CombAlias2.lean`) is built beside `name.sem`, the two rows are
loud-refusal rows and their declarations are retired — see "Xcelium audit,
round 6, lane B" at the end of this file.)*
(2) The Icarus bit-split class (`x_dyn`, `x_child`, `assign t[0] = a;`) has
no rows; each would need its own declaration. (3) Initializer
over-refusals, all loud: an x/z literal at a parameter-dependent width, an
x/z sign bit, a negated literal (`= -2`), an ANSI `output var [1:0]`
(implicit type: dimensions not recovered). (4) The `always_ff` refusal
makes the common FPGA idiom `logic q = 0; always_ff … q <= …` loud (a
plain `always` writer is admitted); svGolf's 22 sources do not use it, a
player's design that does is now refused. (5) The non-ANSI `output var
logic … = …;` declaration is admitted without a differential row (Icarus
12.0 does not parse it). (6) `Lhs2.mustW .concat => []` is recorded, not
fixed (CombGuard2's code is outside this lane). (7) A user function called
in an `always_comb` that writes an initialized variable is not inspected;
user calls are `Unsupported` in symbolic procedural code, so such a block
is loud anyway.

### INIT repair round (round 4 verifier, Lane A) — 2026-10-28

The round 4 INIT verifier found three silent wrong values in the
declaration-initializer work above (one a regression of this lane, two
pre-existing in the forms item (1) claimed to cover), one more in
expression context (routed to the folds lane by the verifier, closed here
in the extractor alone, Lane B being mid-repair; no Lean file touched), and
the over-claims that went with them. Extractor changes are
symbolic-only and additive (`_sym_decl_init` rewritten on top of the new
`_sym_decl_literal`/`_sym_literal_extend`, one refusal in
`convert_port_sym`, one `_sym_unsized_xz_widening` hook at the top of
`_sym_conversion`); no Lean file changed, no M0 path was touched.

**(1) Unsized x/z literals in initializers (regression).** The round-4
lowering padded an UNSIZED literal whose high-order bit is x or z with 0
(`output logic [39:0] y = 'bx` read 8 zeros then 32 x; slang's own
conversion constant does the same). IEEE 1800-2023 §5.7.1 extends it with
that bit "to the size of the expression containing the literal constant",
and Icarus 12.0, Xcelium 24.03 and the Yosys 0.53 netlist agree. The
lowering now reads the literal itself (`_sym_decl_literal`, with slang's
`isDeclaredUnsized`) and pads with that bit at a fixed width; at a
parameter-dependent width an unsized literal of ONE repeated x/z bit
(`'bx`, `'hz`) is `Fill` (the initializer is the whole expression, so every
width gives that bit), anything else stays loud. Row `pi_unsized_xz`
(ports and variables, 36 and 40 bits, truncation): before `y =
00000000x…x1`, `z = 00000000z…z0001`, `v = 1000z…z`, `w = 00000000x…x0101`;
after PASS, Icarus = Xcelium = netlist. Rows `pi_unsized_xz_p` at the
default, `N = 1, 8, 40` (`xcheck:agree`).

**(2) A non-ANSI input whose separately declared variable has an
initializer (pre-existing; item (3)'s "closed in hierarchical designs" did
not hold).** `input [1:0] a; logic [1:0] a = 2'b01;` keeps the initializer
on the internal variable, not the port, so `PortConnection:default` never
fired and the `Port` dropped it: the model read `y = b`. §6.5 makes the
design illegal; slang is silent; the tools split — Icarus 12.0 and Xcelium
24.03 resolve both drivers in a child on a parent port (`y = x1, xx, 0x,
x1`), Icarus follows the driver through a parent variable and at the top
where Xcelium still resolves, the Yosys 0.53 netlist keeps `01`, Verilator
5.042 gives the input (and rejects the net form, `%Error-ASSIGNIN`). Now
`PortSymbol:initialized-input`, top and children, variables and nets.
Rows `pi_in_init` (verifier `n_in5`), `pi_in_init2` (`n_in6`, the
Icarus/Xcelium split the model used to follow silently), `pi_in_top`,
`pi_in_net` (before: loud for an unrelated reason), all loud.

**(3) Plain literal initializers at a parameter-dependent width
(pre-existing).** A literal with NO conversion at the default point (it
has the declared width there, or slang folded a truncation) was emitted as
a default-width `Literal`, which `instDecl` stored unchanged at every
point. A 0/1 literal is now the `Int` of its value (two's complement when
slang types it signed; a signed literal arrives under two implicit
conversions, which `_sym_decl_literal` strips), an x/z literal is `Fill`
or loud as in (1) (`Initializer:x-literal-parametric-width`), and a folded
non-literal at such a width is loud (`Initializer:default-point-literal`).
[CORRECTED, round 5 Lane A, 2026-10-29: "the `Int` of its value" also
took in UNSIZED SIGNED based literals (`'sb1`, `'sh8`, `'shF`, fixed or
parametric width, Var or output Port), on which Icarus 12.0 (sign-extends
the digits: `11111111`) and Xcelium/Verilator/Yosys/§5.7.1 (`00000001`)
split — a silent pick (INIT2 verifier `sbd`, `p4`, `nf`); loud again since
round 5, as at 2e8c8b28.]
Rows `pi_lit_p` at the default and `N = 1, 2, 8, 33` (before at `N = 8`:
`y = 1011`, `z = 1010`, `u` 32 bits; after `00001011`, `11111010`, 36 bits,
Icarus = Xcelium = netlist), `pi_lit_hier` (children of a non-parametric
top, which no cross-check reaches: before `z = 00001` at `a = 1`, `s =
00001010`; after `10001`, `11111010`), `pi_lit_px`/`_n4` and
`pi_uxz_px`/`_n8` loud (before, `pi_lit_px_n4` read the 2-bit `x1` where
the tools give `00x1`).

**(4) Unsized x/z literals in expressions (pre-existing, outside the lane's
files; closed in the extractor).** `assign y = 'bx;` and `a ? 'hz1 :
40'd5` into 40 bits were zero-extending `Resize`s in symbolic mode (the M0
path already had the repair, `_unsized_based_widening_bits`).
`_sym_unsized_xz_widening` pads such an unsigned widened literal to the
context width in a module with one point (row `ux_expr`: before `y =
00000000x…x`, after 40 x, Icarus = Xcelium; Yosys's `prep` constants
`40'hzzzzzzzzz1`/`36'hxxxxxxxxx` agree, its netlist reads x/z as
don't-cares) and refuses it in a family with several points
(`ConversionExpression:unsized-xz`, rows `ux_expr_p`/`_n8`): the padded
value depends on the context width and the literal's own 32 bits take part
in sizing its expression, so not even `Fill` is exact. That refusal is
also an OVER-refusal at points where the 32-bit literal is not widened at
all (`ux_expr_p` at `N = 8` was right before). [CORRECTED, round 5 Lane A,
2026-10-29: "Icarus = Xcelium" holds for assignments and operators, but
the hook also reached INPUT PORT ACTUALS (Icarus 12.0 zero-pads the port,
Xcelium/Yosys extend the x — INIT2 verifier `p8`), CONSTANT positions
(a typed localparam or an override: Icarus x-pads, Yosys and slang
zero-pad) and UNPACKED-ARRAY pattern elements (no Icarus/Yosys oracle;
loud at 2e8c8b28). In each it picked a side silently; all three are loud
since round 5 (the round-5 Lane A entry below).]

**(5) Docs.** The schema's "Converted literal initializers" paragraph and
item (1) above carry CORRECTED notes; the schema gained "Literal
initializers, round 4 repair" (the decision table) and "Unsized x/z
literals in expressions"; the input-initializer sentence is rewritten;
`docs/sv-oracle-disagreements.md` gained "Refused where the oracles split"
(9) and "Refused where the tools agree but `name.sem` cannot follow"
(3)/(4).

**Measured.** Xcelium 24.03 (refsim on vip-ng, one batch of the 22 row
testbenches) equals Icarus 12.0 on every cycle of every admitted row and of
`pi_in_init`, `pi_in_net`, `pi_lit_px*`, `pi_uxz_px*`, `ux_expr_p*`; it
differs on `pi_in_init2` and `pi_in_top` (the split above). The Yosys 0.53
netlist equals Icarus on every initializer row. Before-traces: runner2 on
envelopes from a copy of the extractor with this repair reverted
(`gaps4/ifix/before.log`). The 22 rows (12 PASS, 7 cross-checked points
agree; 10 loud with their kinds) ran green in a scoped `diff_test2`.
Extractor suite from the repo root (final tree, Lane B's tests included):
1817 passed, 3 skipped, 1 failed — the known-flaky
`test_empty_associative_delete::test_symbolic_mode_stays_loud` (2 of 4
reruns fail; flaky at HEAD too);
`test_sym_initializers.py` 42 tests (16 new, one adjusted: `output var
[1:0] y4 = 2'b10` has unrecovered dimensions, so its literal is now its
`Int`). Re-extraction: 230 same, 0 diff, 3 skipped (cv32e40p); no existing
envelope changed, the four committed probe sidecars regenerate
byte-identically, and svGolf's 57 task and test sources (`tb.sv` aside)
extract byte-identically with and without the repair. One slot build of
the round's module list, the ∀-N proofs, the `load_design_sv2` proof users
(with `unary_plus`) and the nine `agree.lean` files: 74 jobs, green, 28
`#print axioms` within `[propext, Classical.choice, Quot.sound]`.
`python3 harness/sv/diff_test2.py --sim iverilog` (one slot run, 477 cases
with Lane B's concurrent rows): 343 verified, 21 declared simulator
disagreements, 24 skipped (23 unavailable Icarus backends), 89 loud
refusals, 0 FAIL, 0 ERROR, 0 `XCHECK-FAIL`; 232 cross-checked row points
agree, 2 unconfirmed but simulator-verified (pre-existing).
`test_oracle_disagreements.py` OK, `sv_divergence_probe.py` PASS,
`divergence_register.py` OK, `docs_check.py` clean.

**Gaps.** (1) `ux_expr_p`-style over-refusal: an unsized x/z literal in a
family is loud even at points where it is not widened. (2) A signed
literal with an x/z sign bit (`'sbx`, `4'sbx01`) stays loud. (3) An x/z
literal at a parameter-dependent width other than a one-bit-repeated
unsized one stays loud. (4) The verifier's minor about
`LeanModels/Python/PayloadBlind.lean` (the `alu_div`/`ff_one`/`popcnt`
`ingest.lean` files import the umbrella and do not build) is outside this
lane and reported, not fixed.

## Default-point folds, round 4 (Lane B: root contexts and genvar initializers) — 2026-10-28

The round 3 FOLDS verifier found three silent wrong values in the constant
tier's root contexts, two of them regressions of the round 3 repair (its
transparent `ctype` plus the pushed-chain floor `PExpr.chainInfo`/
`rootType`). The floor is gone: no root is evaluated at a width read off a
conversion, whose width is the DEFAULT point's. [Round 5 correction: FALSE
as written — `ctype`'s `Squash2` arm still read the 2-state conversion's
default-point width as a floor (`localparam bit [N-1:0] B1 = (U + 1'b1) >>
1` was 8 at `N = 4`, where both tools give 0; verifier repro `vq_sq2`);
repaired in "Default-point folds, round 5" below.] `docs/sv-envelope-schema.md`,
"Default-point folds, round 4", is the reference.

1. **Self-determined roots** (major, regression; verifier repros `rf_lbl`,
   `rf_gen`, `rf_lp`, `rf_par`). With `parameter logic signed [N-1:0] SB =
   -1` (default `N = 8`) slang's tree of `SB + 1'b1` is `Resize(8, SB) +
   Resize(8, 1'b1)` — the round 3 signed-operand marker and a widened
   literal, both at the default point's widest-operand width — and
   `chainInfo` read "every leaf a conversion" as a pushed-down 8-bit target:
   `v[SB + 1'b1]` read v[16] at `N = 4`, `if (SB + 1'b1)` took the then
   branch, an untyped `localparam X = (SB + 1'b1) >> 1` and parameter default
   were 8, where Icarus 12.0 and the Yosys 0.53 netlist agree on v[0], the
   else branch and 0. `evalSized` now evaluates every root at its OWN type at
   the point (`ctype`, then `evalAt`).
2. **INT-class targets** (major, regression; repros `rf_int`, `rf_ipar`).
   `localparam integer L = U + 1'b1` and `parameter integer P = U + 1'b1`
   with `logic [N-1:0] U = -1` (default `N = 32`: no conversion to read)
   were evaluated at U's own width, 0 at `N = 4` and `N = 8`, where Icarus and
   Yosys give 16 and 256. An `integer`/`int` localparam or parameter default
   is now an assignment to a 32-bit target (`evalIntTarget`: `evalAssign 32`
   outside the INT class; an INT-class tree, or the `Squash2` of an `int`
   target around one, keeps `evalInt`), like a typed vector target
   (`evalAssign`). `bindLocal` no longer evaluates a typed initializer with
   `evalInt` first.
3. **Genvar initializers** (major, oracle split; repro `rf_gv`).
   `for (genvar g = U + 1'b1; g < 17; g++)` with `logic [N-1:0] U = -1`,
   default `N = 32`: at `N = 4` Icarus starts at 0 (its own 4-bit width),
   slang's elaboration and the Yosys netlist at 16 (the genvar's 32-bit
   `integer` target, §10.8/§11.8.1), and the model silently followed Icarus
   (HEAD 2e8c8b28 followed slang/Yosys, equally silently). The extractor
   keeps the assignment (`_sym_genvar_init`): an initializer outside the INT
   class at some point (`_sym_genvar_int_class`, stricter than
   `_sym_bound_int_class`, which takes a `logic signed [N-1:0]` parameter
   for an `int` because it is 32 bits at `N = 32`) whose root conversion
   slang made same-width, or that has none, is wrapped in `Resize(32, …)`
   (`SignedResize(32, …)` for a signed operand). Lean reads a conversion AT
   a root as an outside target (`PExpr.pushedTarget`) and uses it only to
   REFUSE: the own-width value where the target's reading agrees,
   `Constant:assignment-context` where it differs. Found while measuring:
   (a) the signed twin, `genvar h = S + S`
   with a 4-bit signed `S = 7`, -2 against 14; (b) an initializer whose value
   is no 32-bit signed integer (`genvar m = U` with a 40-bit `U = 2^40 - 1`,
   or a 32-bit unsigned `U = 2^32 - 1`): Icarus AND Yosys keep it whole (no
   iteration), slang and §27.4 convert it to the `integer` (m starts at -1) —
   refused too (the check is keyed on the 32-bit target, so an instance
   override of such a value into a 32-bit typed parameter is refused alike,
   a recorded over-refusal); (c) an INT-class instance override into a typed
   parameter wider than 32 bits (`.P(N * 1024)` into `logic signed [39:0]
   P`, admitted by round 3 as INT class): on a 32-bit overflow (N = 2^21)
   Icarus gives the 40-bit value, the Yosys netlist the 32-bit wrap, and the
   round 3 floor followed Icarus silently. `_sym_override_root` now keeps
   that assignment as a root conversion of the parameter's width, refused
   where the readings differ (rows `fold_rovr*`), and decides the INT
   class at every point (`_sym_genvar_int_class`: an override over a
   `logic signed [N-1:0]` parameter is typed, so refused as round 3's
   `InstanceSymbol:override-context`). A first version also read an
   INT-class chain widened past 32 bits INSIDE a root as a target; the full
   suite caught it on `fold_pneg_n31/n40*` (`a + P * 2`, where the
   widening is a sibling signal's, in a value position) and it was dropped
   — no conversion inside a root is a target. `docs/sv-oracle-disagreements.md`,
   "Refused where the oracles split" (6), (7) and (8).
4. **The round 3 verify-1 majors, re-checked with new repros.** Case items
   `-P`, `P + 2`, `~P` with `int P = -3` (and 5) in a case of `N + 2` bits
   at `N = 7, 31, 40` (`fold_rcase*`): the model and Icarus zero-extend P
   into the wide case; Yosys differs only by the recorded synthesis-side
   divergence 3 (own-width items). Typed localparams `~4'd0`, `-4'd1`,
   `4'd8 * 4'd4`, `(4'd15 + 4'd1) >> 1` into `logic [N-1:0]`, slang's
   default-point truncation at `N = 2`, at `N = 3, 4, 8, 16` (`fold_rlp*`):
   PASS, Yosys agrees. The UNWRAPPED encoding `_sym_unsigned_simple_operand`
   keeps for a same-width assignment-like conversion,
   `localparam logic [N-1:0] L1 = P` at the default `N = 32`, sign-extends at
   `N = 40` in the model, Icarus and Yosys (`fold_rlpsgn*`).
5. **Over-claims corrected.** The round 3 repair entry's floor sentence and
   its Gap (2) ("exact for a fixed target") carry a correction note; the
   round 3 entry's opening and the schema's round 3 repair section point
   here; `_sym_unsigned_simple_operand`'s docstring now says exactly where
   the marker is emitted (value AND symbolic positions of a family), that
   its width is never read as a context, and why each case it leaves
   unwrapped is exact or loud at every point. [Round 5 correction: its
   "a signed target … the bare reference materializes signed" was exact
   only for a fixed-width operand — a parameter whose default width is 32
   lost its `signed` field (verifier repro `vq_sgn2`); fixed and restated
   in round 5.]

**Measured.** 45 new rows over 8 new fixtures (`sem2/fold_rself`, `fold_rint`,
`fold_rgv`, `fold_rgvw`, `fold_rovr`, and the confirmation fixtures
`fold_rcase`, `fold_rlp`, `fold_rlpsgn`), `harness/sv/cases2.json`
append-only (370 → 415): 36 PASS against Icarus 12.0 with the cross-check
agreeing at every row point — `fold_rself*` (N = 8, 2, 4, 12, 40; N = 4 with
SB = 3), `fold_rint*` (N = 32, 4, 8, 40; N = 4 with U = 3), `fold_rgv*`
(default, N = 4, 40; N = 4 with S = 3; U = -1 at N = 32, 40), `fold_rgvw*`
(default, N = 40; N = 4 with U = -1; N = 40 with U = 5), `fold_rovr*` (N =
5, -7, 2^21 - 1), `fold_rcase*`, `fold_rlp*`, `fold_rlpsgn*` (above) — and
9 loud refusal rows (`Constant:assignment-context`: `fold_rgv_n4_um1`,
`_n8_um1`, `_n4_s7`, `fold_rgvw_n40_um1`, `_n33_um1`, `_n32_um1`,
`fold_rovr_n2097152`, `_n4194304`, `_nm2097153`). The Yosys 0.53 netlist
(`synth -flatten; abc`, simulated in Icarus with each row's testbench; a
negative override of a parameter wider than 32 bits passed to `chparam` at
the parameter's own width) agrees with every PASS row on every cycle except
`fold_rcase_n31/n40/n40_p5` (synthesis-side divergence 3), and splits
from Icarus exactly at the refused `fold_rovr` points; at the refused
genvar points the oracles split as recorded (Icarus, Yosys and slang's
point elaboration). Before the fix, on the round 3 tree: `rf_lbl` (N = 2,
4), `rf_gen`, `rf_par`, `rf_int` (N = 4, 8), `rf_ipar`, `rf_gv` and the new
`fold_rself_n2/n4`, `fold_rint_n4/n8`, `fold_rgv_n4_um1/n8_um1` were silent
default-point folds (`XCHECK FAIL … SILENT default-point fold`, the
envelope reading v[16] for v[0], L = 0 for 16, g from 0 for 16) and
`fold_rgv_n4_s7` ran (Icarus's reading) where it is now refused; the
`fold_rovr` overflow reading of the round 3 floor (Icarus's) and
`fold_rgvw`'s whole-value reading (Icarus's and Yosys's) follow from the
old rules and were not re-run. The verifier's passing and loud repros
(`rf_case`, `rf_val`, `vz_p`, `dq_asc`, `dq_2d`, `pc_carry`, `vz_sgn`,
31 rows) keep their verdicts. Full `python3 harness/sv/diff_test2.py --sim
iverilog`: 415 cases, 298 verified, 21 declared simulator disagreements,
24 skipped (23 unavailable Icarus backends), 72 loud refusals, 0 failed, 0
ERROR, exit 0; cross-check 197 row points agree, 2 unconfirmed but
simulator-verified (pre-existing). CX sweep (95 envelopes, 1671 entries):
every one of the round 3 sweep's 1463 entries keeps its verdict (the first
version of this change flipped five `fold_pneg` points, item 3(c)); of
the 208 new entries 168 agree, 10 are the refused genvar points of
`fold_rgv`, 1 the refused `fold_rovr` point, 9 `fold_rlpsgn` at N ≤ 16
(the point extraction refuses slang's signed truncation there,
`ConversionExpression:width`, so no row is claimed), 10 Lane A's
`pi_width_px`, and 10 UNCONFIRMED `fold_rself` overrides of the untyped
`Y` (`ParamRef:override-type`). reext: 212 same, 0 diff (3 cv32e40p
skipped) — no existing envelope changes; the 8 new fixture envelopes are
the only new ones. Extractor suite 1797 passed, 3 skipped (`PYTHONHASHSEED`
7; seed 11 hits the pre-existing flaky
`test_empty_associative_delete::test_symbolic_mode_stays_loud` in 2 of 3
runs); new `test_sym_folds4.py`. One slot build of the SV modules, the ∀-N
proofs, every buildable `agree.lean` and `load_design_sv2` user (75 jobs)
is green with every statement unchanged; all 28 `#print axioms` within
[propext, Classical.choice, Quot.sound]; new `#guard`s in `Param.lean`
pin the self-determined roots, `evalIntTarget`, the genvar and override
root refusals and the 32-bit fit check. `docs_check` clean,
`divergence_register` OK.

**Gaps.** (1) Pre-existing, verifier minor, not addressed: an untyped
constant whose self-determined value overflows (`localparam Y = SB + 1'b1`)
is 256 in Icarus 12.0 (lossless) and 0 in the model, the Yosys netlist and
§6.20.2/§11.8.1 — undeclared, so no row of that shape is admitted to
`cases2.json` (the round 4 fixtures avoid it). [Round 5: refused,
`Constant:untyped-overflow`.] (2) The 32-bit fit check
over-refuses an instance override of a value that is no 32-bit signed
integer into a 32-bit typed parameter, and the INT-class-chain target of an
override into a parameter whose own type is parameter-dependent is the
default point's (only the refusal side uses it). [Round 5 correction: the
refusal side MISSED the split there, so the model ran silently — verifier
repro `vq_ovr2`, 0 where Icarus gives -2^40; such an override is refused
since round 5.] (3) A genvar initializer
of the INT class keeps `evalInt`'s unbounded reading (the documented
`int32Agrees` restriction), and an INT-class leaf widened past 32 bits
INSIDE a constant root is read at 32 bits (value positions re-evaluate at
the operation width, `constAtCtx2`). (4) The legacy-select range guard and
`_sym_override_root`'s over-refusal of width-neutral typed overrides stay
as documented (verifier minors, optional). (5) svGolf (a separate lake
project) was not rebuilt here; the 3 cv32e40p envelopes are reext SKIP.
(6) A negative override of a parameter wider than 32 bits must be passed
to Yosys `chparam` at the parameter's width (a `32'sh…` value is not
sign-extended): the measuring script `oracles.py` was corrected for it.

## Default-point folds, round 5 (Lane B repair: 2-state targets, declared signedness, dependent overrides, untyped wraps) — 2026-10-28

The round 4 FOLDS verifier found three blockers: two silent wrong values
that round 4's claim "no root is evaluated at a width read off a
conversion" had missed, and one oracle split that the model followed
silently. It also found three minors. `docs/sv-envelope-schema.md`,
"Default-point folds, round 5", is the reference.
`docs/sv-oracle-disagreements.md`, "Refused where the oracles split",
items (10) and (11), records the splits.

1. **`Squash2` was a floor** (blocker; verifier repro `vq_sq2`; a HEAD-era
   rule that rounds 3 and 4 kept). slang wraps the initializer of a
   2-state target in a same-width 4-state → 2-state conversion sized at
   the DEFAULT point. `ctype` read it as `max(that width, the operand's
   width)`. Take `localparam bit [N-1:0] B1 = (U + 1'b1) >> 1`, `B2 = (U +
   1'b1) % 3'd5`, `B3 = (U + 1'b1) >>> 2` and `parameter bit [N-1:0] PB =
   (U + 1'b1) >> 1`, with `logic [N-1:0] U = -1` and default `N = 32`.
   The model gave 8, 1, 4, 8 at `N = 4` and 128, 1, 64, 128 at `N = 8`.
   Icarus 12.0 and the Yosys 0.53 netlist give 0 for all four. `ctype` is
   now transparent to `Squash2`, as it is to `Resize`. The target comes
   from `evalAssign` (the declared width) or `evalIntTarget` (`int`).
   *(Round 6 correction: this fixed a `Squash2` at the root and introduced
   a silent wrong value under a NARROWING target, `Resize(target,
   Squash2(…))`: the context stopped at the `Squash2`, so `localparam
   shortint H1 = (U + 1'b1) >> 1` became 0 at a 4-bit `U = 15` where HEAD,
   round 4 and every tool give 8. See "Default-point folds, round 6".)*
2. **Signedness was folded at the default point** (blocker; present at
   HEAD). `_sym_param_signedness` emitted `signed` only where the type
   departed from "signed exactly when 32 bits wide" AT THE DEFAULT POINT.
   `declConstType` then applied that rule at each point's width.
   * `parameter logic signed [M-1:0] S = -1` (default `M = 32`) was read
     UNSIGNED at `M = 8` (verifier repro `vq_sgn2`). `assign o1 = S` gave
     255 where both tools give 2^64 - 1. `localparam integer I = S >>> 1`
     gave 127 where both tools give -1. `S < 0` gave 0.
   * `logic [N-1:0] U` (default `N = 8`) was read SIGNED at `N = 32`
     (`vq_sgn3`); `int32Agrees` made it loud there.

   The extractor now always emits `signed` for a type whose width depends
   on a parameter. `declConstType` refuses a type with a non-literal bound
   and no field, so a stale envelope cannot be read by the one-width rule.
   Re-extraction adds `"signed": false` to seven existing envelopes:
   `fold_cgrow`, `fold_lpgrow`, `fold_lpshr`, `fold_ovr`, `fold_ovr2`,
   `fold_psel` and `fold_rlp`. All seven are unsigned, so their
   default-point reading is unchanged. No other envelope or probe sidecar
   changes.
3. **An INT-class override into a parameter of dependent width**
   (blocker, oracle split; verifier repro `vq_ovr2`). Take `#(.W(N + 40),
   .P(N << 40))` into `logic signed [W-1:0] P`, with default `N = 0`.
   Round 4's root conversion carried the default point's 40 bits, where
   the 32-bit and 40-bit readings agree on 0. At `N = 1`, P is 41 bits:
   Icarus 12.0, §10.8 and slang give -2^40, and the Yosys netlist gives 0.
   At `N = 24` it is 24·2^40 against 0. The refusal side MISSED the split
   and the model ran, so round 4 Gap (2) was wrong to call this case
   refusal-only.
   `_sym_override_root` now refuses (`InstanceSymbol:override-context`) an
   INT-class context-propagating override into a child parameter whose
   declared width is not fixed. `_sym_param_type_fixed` counts a type as
   fixed when it is a keyword integral or implicit type whose bounds are
   built from integer literals and from sibling parameters that are
   literal at every point (`.W(40)`, or a literal default that is not
   overridden), or when the parameter is untyped. These stay admitted:
   leaves (`.P(N)`), fixed-width targets (`fold_rovr`), `int` targets, and
   the verifier's `vq_ovr` `u4` (`.W(40)`). A first version refused `u4`,
   which turned `vq_ovr` default, `N = 7` and `N = -7` loud where they had
   passed. The sibling-literal clause fixed that.
4. **Over-claims** (minor). These now carry round 5 correction notes:
   * in the round 4 entry: "no root is evaluated at a width read off a
     conversion", its Gaps (1) and (2), and item 5's docstring claim;
   * the schema's round 3 and round 4 sections.

   `_sym_unsigned_simple_operand`'s docstring now says the bare signed
   reference is exact because the declared signedness is recorded at
   every point (since round 5), and that it was exact only for fixed-width
   operands before.
5. **`_sym_bound_int_class`** (minor) had no caller left after round 4. It
   was added in round 3 (it is not at HEAD), so it is removed.
6. **Untyped constants that wrap** (minor; round 3 verifier minor 4; the
   tools split). `localparam Y = SB + 1'b1` with an 8-bit `SB = 255` is 0
   in slang, §6.20.2 and the Yosys netlist, and 256 in Icarus 12.0, which
   evaluates an untyped parameter value losslessly.
   * **Measured** with probes, the Icarus traces checked against Yosys
     netlists: Icarus widens through `+ - * / **`, unary `-` and the arms
     of `?:`, and stops at shifts, comparisons, casts and selects. The
     width differs too: `$bits(X)` is 65 in Icarus and 40 in Yosys for `X
     = U + N * 1024`. *(Round 7 correction: at right shifts and at a sized
     left operand; a left shift of an unsized or INT-class operand widens,
     `1 << N` is 2^40 at `N = 40` in Icarus.)*
   * **The fix.** New `evalUntyped`, for untyped parameter defaults and
     localparams. It refuses (`Constant:untyped-overflow`) wherever the
     own-type value differs from its reading at 64 more bits, with shifts
     kept at their own width.
   * **Soundness.** It refuses every measured split. It over-refuses where
     Icarus happens to keep the bits (`-SB`, `~SB`, `~(SB + 1'b1)`).
     *(Round 6 correction: it did not. The same entry measured the WIDTH
     split (`$bits` 65 against 40) without refusing it; the width splits
     where no value wraps (`(Y + 8'd255) >> 1` into 8 bits: 130 against 2
     at `SB = 5`) and in the INT class (`N + 1` is 33 bits in Icarus); and
     a wrap beyond 64 extra bits (`2 ** SB` at `SB = 100`) escaped. See
     "Default-point folds, round 6".)*
   * **What it changes.** The shift barrier keeps `fold_rself`'s untyped
     `X = (SB + 1'b1) >> 1` running, since Icarus agrees there. The
     verifier's `vq_mix` at `N = -2097153` and at `N = -7, U = 5`, which
     passed on a 40-bit output, is now refused. Its untyped `X` really
     differs: 4395899026432 against 1097364143104, visible at 80 bits.
   * **The pinned `#guard` that changed meaning.** The untyped `L = K +
     3'd7` at `K = 1` (a 3-bit wrap to 0) is now loud. The guard now pins
     `K = 0` (7) and the refusal.

**Measured.** 40 new rows over six new fixtures (`sem2/fold_sq2`,
`fold_psgn`, `fold_psgnw`, `fold_ovrw`, `fold_ovrwl`, `fold_uovf`).
`harness/sv/cases2.json` is append-only (437 → 477, after Lane A's
round 4 repair rows). No existing row was changed.
* 33 rows PASS against Icarus 12.0, with the cross-check agreeing at
  every row point:
  * `fold_sq2*`: default; `N = 0, 1, 2, 4, 8, 31, 33, 64`; `N = 4` with
    `U = 5`.
  * `fold_psgn*`: default; `M = 8`, `M = 4` with `S = -3`, `M = 16` with
    `S = 5`; `N = 32, 16`; `N = 32` with `M = 16`; `M = 8` with `N = 32`.
  * `fold_psgnw*`: default; `M = 40, 33, 64`; `M = 40` with `S = 5`;
    `M = 48` with `S = -3`.
  * `fold_ovrwl*`: default; `N = 1, 24, -5, 100`.
  * `fold_uovf*`: default `SB = 5`; `SB = 100`; `N = 16`; `N = 4` with
    `SB = 3`.
* 7 rows are loud refusals:
  * `InstanceSymbol:override-context`: `fold_ovrw`, `fold_ovrw_n1`,
    `fold_ovrw_n24`.
  * `Constant:untyped-overflow`: `fold_uovf_sb255`, `_sb200`,
    `_n16_sbm1`, `_n4_sb15`.

`fold_psgn` at `M = 40` and `fold_ovrwl` at `N = -30` are not rows. The
point extraction refuses slang's narrowing of `S` into the `integer` and
of `N` into the 10-bit `P` (`ConversionExpression:width`), so they cannot
be cross-checked. `fold_psgnw` covers the wide `M`.

The Yosys 0.53 netlist (`chparam; synth -flatten; abc`, simulated in
Icarus) agrees with Icarus on every 0/1 cycle of every PASS row. It splits
from Icarus exactly at the refused points:
* `fold_ovrw`: 0 against -2^40 at `N = 1`;
* `fold_uovf`: 0 against 256, 144 against 400, and so on.

Before the fix, on the round 4 tree with the old extractor:
* `fold_sq2_n0` to `n31` FAILED against Icarus (8, 1, 4, 8 at `N = 4`);
* `fold_psgn` at `M = 8, 4, 40` FAILED (o1 = 255 for 2^64 - 1, I = 127
  for -1);
* `fold_psgn` at `N = 32` was loud through `int32Agrees`;
* `fold_ovrw` at `N = 1` and `N = 24` FAILED (0 for -2^40 and 24·2^40);
* `fold_uovf` at `SB = 255`, `N = 4` and `N = 16, SB = -1` FAILED,
  following the LRM and Yosys silently.

The verifier's 134 repro rows (`vq_*`) were re-run on the final tree,
re-extracted. 25 changed verdict:
* `vq_sq2`, `vq_typ` (`N = 0` to `31`, and `N = 4` with `U = 3`),
  `vq_sgn`, `vq_sgn2` and `vq_sgn3` move from XCHECK-FAIL or ERROR to
  PASS.
* `vq_ovr2` and the two `vq_mix` points above move to loud refusals.

Every other `vq_*` row keeps its verdict. That includes the pre-existing
loud ones and the declared wide-index `vq_idx` disagreement.

Full `python3 harness/sv/diff_test2.py --sim iverilog`: 477 cases, 343
verified, 21 declared simulator disagreements, 24 skipped (23 unavailable
Icarus backends), 89 loud refusals, 0 failed, 0 ERROR, exit 0. The
cross-check had 232 row points agree and 2 unconfirmed but
simulator-verified (pre-existing). reext: 230 same, 0 diff, 3 cv32e40p
skipped. Before regeneration it found exactly the seven `signed`
additions above, and the regenerated files are byte-identical to it.

Extractor suite: 1818 passed, 3 skipped, with `PYTHONHASHSEED=7`; the
new file is `test_sym_folds5.py`. The pre-existing flaky
`test_empty_associative_delete::test_symbolic_mode_stays_loud` failed in
one run and in 2 of 3 runs on its own, under the same seed; it is
unrelated to this change. `Param.lean` gains `#guard`s for the
`Squash2` targets, the `signed` refusal and the declared signedness, and
the untyped-wrap refusal with its shift barrier.

One slot build covered the SV modules, the ∀-N proofs, every `agree.lean`
and every `load_design_sv2` user except the three cv32e40p `ingest.lean`
(see Gaps). It is green (75 jobs) with every statement unchanged, and all
30 reported `#print axioms` are within [propext, Classical.choice,
Quot.sound]. `docs_check` is clean and `divergence_register` reports OK.

**Gaps.**
1. `evalUntyped` over-approximates Icarus's widths: it refuses `-SB`,
   `~SB` and `~(SB + 1'b1)` where Icarus keeps the bits. Its wide reading
   is 64 extra bits, so a wrap that only shows beyond that (a huge `**`)
   is not seen.
2. The fixed-width test is syntactic. A dependent type whose width is in
   fact constant through a non-literal expression is refused, which is an
   over-refusal.
3. The three cv32e40p `ingest.lean` files import the umbrella
   `LeanModels`. The umbrella's Python modules (`LeanModels.Python.Tests`,
   `PayloadBlind`) are unchanged from HEAD, belong to no SV lane, and fail
   to build in this tree, so those three were not built. Their envelopes
   hold no parameter of dependent width, so neither the `signed` refusal
   nor the `Squash2` change can reach them.
4. svGolf (a separate lake project) was not rebuilt here.
5. Round 4's gaps (2, first half) and (3) through (6) stand.

## Initializers and unsized literals, refusal-only (round 5, Lane A) — 2026-10-29

Round 5 is refusal-only and monotone: a fix may add a loud refusal, revert a
round-3/4 change to 2e8c8b28 behaviour where that was loud or correct, or
correct a value only where Icarus 12.0, the Yosys 0.53 netlist and slang's
own elaboration agree on a parameter sweep. Where the tools split, the
design is refused, never decided for one side. This entry closes the round-4
INIT2 verifier's two majors and its minor, plus two further silent picks of
the round-4 expression hook found by this round's own probes. Every change is
an extractor refusal (symbolic mode only, additive; no M0 path touched); no
Lean file changed. Probes and logs:
`/private/tmp/claude-501/-Users-ahle-repos-lean-surfaces/ef50039c-ca19-4962-8585-1ff4626e9462/scratchpad/gaps5/init/`.

**(1) Unsized x/z literals in input port actuals (INIT2 major 1).** The
round-4 hook `_sym_unsized_xz_widening` also rewrote input port actuals,
where the tools split. `.i('hx0)` into a 40-bit port gives 8 zeros, 28 x,
`0000` in Icarus 12.0, which pads the self-determined actual with zeros
("Padding 8 high bits of the port"). Xcelium 24.03 (verifier) and the Yosys
0.53 netlist give 36 x then `0000`. At 2e8c8b28 the model followed Icarus (a
zero-extending `Resize`, row PASS); after round 4 it followed Xcelium and
Yosys (row FAIL against Icarus). Neither choice was recorded. Inside an
input actual (`_sym_port_conn` sets `_SymUnsizedXZLoud`) every such widening
is now `PortConnection:unsized-xz`, whether the literal is bare, under `?:`
or under an operator. [CORRECTED, round 5 repair, 2026-10-29: only where
the port was wider than the literal at the BOUND point (the defaults, the
first generate-for iteration); a port wider only at another point was
admitted with Icarus's padding (verifier `vp1`, `vp2`), and a narrower
default folded the actual (`vp7`). Since the repair any actual holding an
unsized x/z-top literal is refused — "Unsized x/z literals at every
point" below.] Fixture and refusal row: `pa_unsized_xz`. The schema
paragraph, the round-4 entry (4) above and the hook's docstring carry
CORRECTED notes on the "Icarus agrees" claim.

**(2) Unsized signed based literals (INIT2 major 2, plus its expression
twin).** Icarus 12.0 sizes `'sb1`, `'sh8` and `'shF` to their digits and
sign-extends them in every context measured: an initializer, an
assignment, `a + 'sb1`, `localparam P = 'sh8` (-8), an index, a comparison,
a `case` item and `>>>`. In 8 bits `'sb1` is `11111111` and `'sh8` is
`11111000`. Verilator 5.042, the Yosys 0.53 netlist, Xcelium 24.03
(initializers) and §5.7.1 give `00000001` and `00001000`.

- At 2e8c8b28, initializers were loud: a `SignedResize` that `instDecl`
  refused. Expressions were admitted with the LRM value, a silent pick
  against the harness oracle (`head_ux_signed` FAILs against Icarus).
- Round 4 made initializers admitted `Int`s (`r4_pi_unsized_signed` FAILs).
- Now a declaration or output-port initializer is `Initializer:unsized-signed`
  (`_sym_decl_init`).
- Every such token in the compiled sources adds `IntegerLiteral:unsized-signed`
  to the top's `others` (`_sym_unsized_signed_scan`, a syntax scan). This is
  the one choke point for the class: a fold or a direct literal read, such as
  an index, would bypass a per-expression check.

Fixtures and refusal rows: `pi_unsized_signed`, `pi_unsized_signed_n32` and
`ux_signed`.

**(3) Two more silent picks of the round-4 hook (found here).**

- **CONSTANT positions** (`_SymPos`). A `case` item `'hx0` over a 40-bit `b`
  is x-padded by Icarus and Yosys `prep`, but the Yosys netlist reads the x as
  a don't-care: at `b = 00000000` then 28 x then `0000`, Icarus gives 2 and
  the netlist 1. 2e8c8b28 zero-padded the item and was wrong against both
  tools at `b = x…0000`; round 4 followed Icarus. It is now
  `ConversionExpression:unsized-xz-constant`.
  - Parameter values and overrides (`localparam logic [39:0] LP = 'hx0`,
    `#(.P('hz1))`, an untyped `LQ = 'hx0`) split as well: Icarus against Yosys
    and slang's constant. They were loud in the Lean constant tier ("x/z
    literal in a constant context") at 2e8c8b28, in round 4 and now.
  - Fixture and refusal row: `ux_const`.
- **Unpacked-array pattern elements** (`logic [39:0] m [0:1] = '{'hx0,
  'hz1}`, verifier `ap`). Icarus does not support the declaration and Yosys
  does not parse it, so there is no oracle. 2e8c8b28 refused it as a
  "non-literal initializer"; round 4 admitted it.
  - It is now `Initializer:unsized-xz-element` on the declaration
    (`convert_fixed_array_vars_sym`).
  - Fixture and refusal row: `ux_array`.

**(4) Nested-instance refusal naming (INIT2 minor): accepted as worded.**
`Process2.inInstance` gives one clause per level, outermost first. It does
not print one flattened path. Measured through `load_design_sv2` on `nest` →
`mm` (`nest_m`) → generate block `g` → `ll` (`nest_l`):

> in instance 'mm' of module 'nest_m' (its signals flatten under the prefix
> 'mm.' inside the module that instantiates it): in instance 'll' of module
> 'nest_l' (its signals flatten under the prefix 'g.ll.' inside the module
> that instantiates it): always_comb block reads bit [1] of 't' …

The leaf's flattened signal is `mm.g.ll.t`: the clauses' prefixes
concatenated outermost first. The schema's self-read paragraph now says
exactly this. Threading the accumulated prefix would change `ChildInst`,
which the `fa_flatten` proof simplifies through, and `Hier2.lean` was not
touched.

**(5) Re-checks.**

- **Round-4 closures hold.**
  - Non-ANSI output-port initializers (`reg`, `logic`, `var logic`; converted,
    signed, unsized x/z and sized x forms; probe `rc1b`) PASS against Icarus
    and equal the Yosys netlist.
  - The §6.5 mixtures stay refused (probes `rc2`, `rc3`). These include a
    non-ANSI initialized input two levels down, an `assign` to a bit of an
    initialized variable, a child output into an initialized variable, a
    streaming target and a struct-member target.
  - Unsized x/z in declarations and expressions wider than 32 bits equals
    Icarus and the Yosys netlist (probes `uf`, `uxc`, `ni`; nets are loud
    anyway for packed dimensions). [CORRECTED, round 5 repair, 2026-10-29:
    true of declaration initializers and of modules with one point only.
    In a family the expression value was fixed at the default point and
    wrong against both tools at other points (verifier `vp3`, `vp4`,
    `vp6`, `vp8`, `vp9`), and `$unsigned('hz1)` widened splits Icarus from
    the netlist even with one point (`ex3`) — "Unsized x/z literals at
    every point" below.]
  - The `FailsClosed` tests pass.
- **Refusal sets, 2e8c8b28 against the current extractor.** The comparison
  covered every sem2 fixture, the round-3/4 INIT repro directories and these
  probes (450 tops). The 2e8c8b28-loud shapes in this lane that are admitted
  now:
  - converted 0/1 literal initializers (`pi_width_forms`, `pi_width_p`,
    `pi_lit_p`);
  - unsized unsigned x/z initializers at a fixed width (`pi_unsized_xz`,
    `w_var2`);
  - their `Fill` at a parameter-dependent width (`pi_unsized_xz_p`).

  `pi_lit_p`, `pi_unsized_xz_p` and `pi_width_p` were swept at the default
  and `N` = 0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 33, 63, 64, 65. All 48
  points PASS against Icarus with xcheck agree (slang's elaboration at the
  point), and the Yosys netlist traces equal Icarus's at every point. The
  remaining differences are Lane B's (`fold_psgn`, `fold_psgnw`,
  `fold_query`).

**Verification.**

- **Build.** One slot build was green: 74 jobs, with every statement
  unchanged.
  - It covered LeanModels.Sv.{Ingest2, Probe2, Param, Param2, RangeGuard2,
    Gen2, Hier2, Hier2Gen, CombGuard2, CombGuard2Sound, Comb2Example,
    Comb2ConcatExample, Comb2Proc, Comb2ProcExample, Mono2, SelfCheck}.
  - It also covered the ∀-N files (ripple_add gen/proof/spec, mul2d,
    partsel, ripple_fa), the `load_design_sv2` proof users and all nine sem2
    `agree.lean`.
  - All 28 `#print axioms` reports are within [propext, Classical.choice,
    Quot.sound].
- **Extractor suite.** On the final tree, 1835 passed and 3 skipped, in
  three consecutive runs. In one earlier run,
  `test_symbolic_instances::test_generate_loop_instance` and the known-flaky
  `test_empty_associative_delete` each failed once; the first passes alone.
  `test_sym_initializers.py` has 52 tests (10 new, 2 adjusted to the
  restored refusals).
- **reext and sidecars.** reext gave 246 same, 0 diff and 3 cv32e40p
  skipped, with Lane B's round-6 fixtures in the tree; the only envelopes
  this entry creates are the five new fixtures. The four committed probe
  sidecars regenerate byte-identically.
- **docs_check.** Clean.
- **Full `diff_test2 --sim iverilog`.** EXIT 0 on the tree after Lane B
  corrected its rows: 0 FAIL, 0 ERROR.
  - 378 verified, 21 declared, 124 loud (the six new rows included), 24
    skipped, 23 unavailable.
  - Cross-check: 263 row points agree, 2 unconfirmed (pre-existing).
  - A first run, made before Lane B updated its `Constant:untyped-width`
    rows, failed only those 9 rows (`register_file_ff`, `fold_uovf*`).

**Gaps.**

1. `PortConnection:unsized-xz` over-refuses an actual whose own width
   already reaches the port (`s ? 'hx0 : 40'd5`, `'hx0 ^ b` with a 40-bit
   `b`). It also over-refuses a widening inside a comparison within an
   actual. The tools agree on both.
2. `IntegerLiteral:unsized-signed` over-refuses `'sd…` and literals whose
   top digit bit is 0 (`'sb01`), where the tools agree. Because it is a
   scan of every compiled file, it also refuses literals in modules the top
   never instantiates.
3. `ConversionExpression:unsized-xz-constant` covers selects and generate
   headers with no measured split there.
4. The nested-instance message keeps its per-level clauses (4).
5. Xcelium was not re-run in this round. Its values are the round-4
   verifier's (`p8`, `sbd`).

## Default-point folds, round 6 (Lane B, refusal-only: `Squash2` under a narrowing target, typedef widths, enum values, untyped widths) — 2026-10-29

Under the round 5 rule (refusal-only and monotone), this round closes the
round 5 FOLDS verifier's four findings and the class behind its two
blockers: a width, bound, value or conversion that the envelope fixes at
the DEFAULT point and Lean then uses at other points without recomputing
it. Nothing that was loud is admitted. The one corrected computation is
equal to Icarus 12.0, the Yosys 0.53 netlist and slang's own elaboration
at every row point (and five more in scratch). *(Round 7 correction: one
loud shape was admitted by item 1 — a `Squash2` operand that divides by
zero at its own width but not at the context; it is loud again, see
"Default-point folds, round 7".)* Everything else is a new
loud refusal. `docs/sv-envelope-schema.md`, "Default-point folds, round
6", is the reference; `docs/sv-oracle-disagreements.md`, items (12) and
(13), records the two new oracle splits.

1. **The context reaches through a `Squash2`** (blocker; a regression of
   round 5; verifier repro `vs_sqn`). Round 5 made `ctype` read `Squash2`
   as its operand's type but left `PExpr.ctxPropagates (.squash2 ..)`
   false. A 2-state target NARROWER than its initializer at the default
   point is `Resize(target, Squash2(default width, op))`, and the
   `resize` arm then evaluated `op` at its own width where the target is
   the wider context. With `logic [N-1:0] U = -1` (default `N = 32`), at
   `N = 4`: `localparam shortint H1 = (U + 1'b1) >> 1` was 0 where Icarus,
   the Yosys netlist and slang give 8; `byte Y1 = U + 1'b1` 0 for 16; `bit
   [7:0]`, `bit signed [7:0]` and a `byte` parameter default 0 for 8; and
   `localparam int KI = (UK + 1'b1) >> 1` (default 40-bit `UK`) 0 for 8 at
   `K = 4`. HEAD and round 4 gave the right value here. Fix (rule (c)):
   `ctxPropagates (.squash2 _ a) = a.ctxPropagates`. The value tier
   refuses every `Squash2`, so only the constant tier reads it.
   *(Round 7 correction: this also admitted `localparam shortint H1 =
   4'd8 / (U + 1'b1)` at a 4-bit `U = 15`, which divides by zero at U's
   own 4 bits — loud in round 5 — and gives 0 at the 16-bit context. The
   own-width reading is now required to be defined; see round 7, item 4.)*
   * **Three-way measurement** (`slang3.py`, scratch `gaps5/folds`): the
     nine outputs of `fold_sqn` (H1, Y1, B8, S8, L8, KI, PY, W40, LL) agree
     between slang's elaborated value, Icarus and the Yosys netlist at the
     default and at `N = 0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 33, 63, 64, 65`,
     `K = 4, 8, 15, 16, 31, 32, 33, 63, 64, 65`, `N = 4, U = 5`, `K = 4,
     UK = 5`, `N = 8, U = 100`. The model PASSES at all of them. Before,
     at the same shapes: the verifier's `run2n.log` (0 for 8, 16, 128,
     2^30).
   * `Param.lean` `#guard`s pin H1 = 8, KI = 8, Y1 = 16 and the `byte`
     default PY = 8 at a 4-bit `U = 15`, and H1 = 0 at a 33-bit operand.
2. **A named parameter type of point-dependent width** (blocker; present
   at HEAD; verifier repros `vs_td2`, `vs_td4`). `typedef logic signed
   [M-1:0] st_t; localparam st_t TS = -1;` has no dimensions in its type
   syntax, so `_param_width_type` emitted slang's elaborated bounds, the
   default point's `[31:0]`, with no `ParamRef` for round 5's
   `PType.boundsLiteral` guard to see. With the round 5 extractor `TS + a`
   (a = 15) was 4294967310 at every M where both tools give 16, 30, 270,
   2147483662, 1099511627790 and 14 at `M = 1, 4, 8, 31, 40, 64`; the
   2-state `bit [M-1:0]` typedef the same. New
   `_sym_param_named_type_point_dependent`: a declared type that is not a
   keyword or implicit type (`_SYM_FIXED_PARAM_TYPE_KINDS`) and whose
   syntax, typedef followed, is point-dependent
   (`_sym_syntax_point_dependent`) becomes `packed: null`, loud as
   "unrecoverable packed dimensions" at every point. Fixed-width typedefs,
   and any typedef in a family with one point, keep their bounds.
3. **Enum member values fixed at the default point** (the class, found by
   the search; present at HEAD). The `EnumType` node carries each member's
   default-point value, and Lean bound those at every point: `typedef enum
   logic [7:0] {EA = N, EB = N + 2}` (default `N = 3`) read EB = 5 at
   `N = 5`, where both tools give 7, and at `N = 0`, where they give 2. New
   `_sym_enum_values_point_dependent`: a reference to a member of a module
   enum with a point-dependent member initializer is `Unsupported`
   (`EnumValueSymbol:default-point-value`). Fixed enums and package enums
   keep `EnumRef`; a first version refused package enums too (the
   initializer's names were looked up in the module scope), measured on a
   probe and corrected before any row. *(Round 7 correction: the class is
   wider than named initializers — a member value also depends on the
   point through an unsized literal (`'1`) or a point-dependent base width;
   see round 7, item 2.)*
4. **Untyped constants: the width splits, not only the value** (major
   and minor; verifier repros `vs_uw`, `vs_up`, `vs_uw3`, `vs_upw2`; INT
   class newly measured). Icarus 12.0 (default `-gno-strict-expr-width`)
   gives an untyped parameter or localparam the lossless WIDTH of its
   expression, slang, §6.20.2 and Yosys its own type. Measured with `$bits`
   (scratch `gaps5/folds/p/uw`): one carry bit per `+ -` (`SB + 1'b1` 9,
   `N + 1` 33), the sum for `*`, a base- and value-dependent width for `**`
   (`2 ** N` 32 at `N = 8`, 42 at `N = 40`), carried through `/ % & | ^`,
   unary `- ~ +` and `?:` arms, stopped by shifts, comparisons, casts,
   selects and concatenation parts. *(Round 7 correction: a RIGHT shift
   stops the width; a LEFT shift of an unsized or INT-class operand widens
   it, `1 << N` is 32 + N bits in Icarus. Left shifts are now refused too;
   see round 7, item 3.)* It shows with no wrap: `(Y + 8'd255)
   >> 1` into 8 bits (`Y = SB + 1'b1`, `SB = 5`) is 130 against 2; `{a, B}`
   with `localparam B = N + 1` is `0x1e00000009` against `0xf00000009`;
   `a + C` with `C = N - 9 = -1` into 64 bits is `0x200000002` against
   `0x100000002` at `a = 3`. The model
   followed Yosys silently; at `N = 40`, `{a, E}` with `E = 2 ** N` passed
   even `int32Agrees`, because the 32-bit materialization hid the unbounded
   value. New `PExpr.icarusWidens` in `evalUntyped`: every untyped
   parameter default and localparam built with `+ - * **` on its context
   chain is refused at every point, whatever its value
   (`Constant:untyped-width`). This is a whole-class refusal at one choke
   point. It also covers minor 4 (`2 ** SB` at `SB = 100`, which escaped
   the round 5 check at 64 more bits). A first version exempted an INT-class
   `<unsized literal> ** <INT>` (32 bits in Icarus while the value fits);
   the `N = 40` measurement above refuted it, and it was removed before any
   row.
5. **An INT-class override with `+ - * **` into an untyped child
   parameter** (found by the search). The child parameter takes the
   override's type: 32 bits in slang and Yosys, 33 in Icarus (`.W(N + 1)`
   read as `{a, W}`: `0x1e00000009` against `0xf00000009`). The model
   followed Yosys. `_sym_override_root` now refuses it
   (`InstanceSymbol:override-untyped-width`, `_sym_param_untyped`,
   `_sym_icarus_widens`). Leaves and overrides into typed parameters stay.
6. **Over-claims corrected** with round 6 notes: the round 5 entry's
   `Squash2` item ("no root … is read at a conversion's width") and its
   item 6 ("It refuses every measured split"), the schema's round 5
   section (both sentences) and oracle-disagreements item (11).

**Rows** (`harness/sv/cases2.json`, 64 appended over 11 new sem2
fixtures, and 9 existing rows corrected):
* PASS against Icarus 12.0 with the cross-check agreeing (40):
  `fold_sqn*` (23), `fold_tdf*` (5: default, `M = 1, 8, 40, 64`),
  `fold_uwok*` (5: default, `N = 0, 1, 30, 40`), `fold_uwovl*` (3:
  default, `N = 0, 31`), `fold_enf*` (4: default, `N = 4, 16, 40`). The
  Yosys netlist agrees with Icarus on every cycle of every one.
* Loud refusal rows, each with a `measured` field (24): `fold_tdw*` (7,
  "unrecoverable packed dimensions"), `fold_uwid*` (4), `fold_uwidp*` (5)
  and `fold_uwint*` (3) (`Constant:untyped-width`), `fold_uwovr*` (2,
  `InstanceSymbol:override-untyped-width`), `fold_enm*` (3,
  `EnumValueSymbol:default-point-value`).
* **Corrected rows** (the refusal reaches them; the rule allows only
  refusals, so each says why): `fold_uovf`, `_sb100`, `_n16`, `_n4_sb3`
  (PASS → `Constant:untyped-width`, over-refusals: 64-bit reads where the
  tools agree); `fold_uovf_sb255`, `_sb200`, `_n16_sbm1`, `_n4_sb15` (kind
  `Constant:untyped-overflow` → `Constant:untyped-width`, refused earlier
  by the new check); `register_file_ff` (PASS → `Constant:untyped-width`,
  an over-refusal: the cv32e40p register file's untyped `NUM_TOT_WORDS`,
  built with `+`, is read only in dimension and generate bounds).

**Measured.** Full `python3 harness/sv/diff_test2.py --sim iverilog`: 547
cases, 378 verified, 21 declared simulator disagreements, 24 skipped (23
unavailable Icarus backends), 124 loud refusals, 0 failed, 0 ERROR, exit 0;
the cross-check had 263 row points agree and 2 unconfirmed but
simulator-verified (pre-existing). Against round 5 (477 cases): +40
verified rows here, −5 corrected to refusals; +24 refusal rows here, +5
corrected, +6 from Lane A's round 5 entry. The verifier's repros, re-extracted
and re-run: `vs_sqn` (18 points) and `vs_sq` (11) PASS; `vs_td`, `vs_td2`,
`vs_td4` (21) are loud ("unrecoverable packed dimensions"); `vs_uw`,
`vs_up`, `vs_uw3`, `vs_upw`, `vs_upw2` (15) are loud
(`Constant:untyped-width`). Before, with the round 5 extractor,
`fold_tdw` FAILED at every `M ≠ 32` (o1 = 4294967310 at `M = 8` where
Icarus gives 270); with the round 5 or HEAD extractor `fold_enm` FAILED at
`N = 5` (o1 = 5 for 7) and `N = 0` (5 for 2) and `fold_uwovr` FAILED at
`N = 8` and `N = 0` (the Yosys reading).

reext: 246 same, 0 diff, 3 cv32e40p skipped (the new fixtures included);
the four committed probe sidecars and their envelopes regenerate
byte-identically. No existing envelope changes: no fixture in the corpus
had a point-dependent named parameter type, a point-dependent enum member
or a widening override into an untyped child. Extractor suite: 1834
passed, 3 skipped, 1 failed; `test_sym_folds6.py` is new (7 tests), and one
`test_sym_folds5.py` assertion (`.X(N * 2)` into an untyped `X` admitted)
now asserts the round 6 refusal. The failure is the known-flaky
`test_empty_associative_delete::test_symbolic_mode_stays_loud`, which also
fails and passes on its own from run to run under the same seed; it is
unrelated.
`Param.lean`'s `#guard`s: the round 5 guards that pinned untyped
`L = K + 3'd7` at `K = 0`, `Y = SB + 1'b1` at `SB = 5` and `N + 1` as
values now pin their refusal; the hand-built `gen_sel` smoke design's
`KM1 = K - 1` is now an `int` localparam, with its untyped twin pinned
loud. One slot build (75 jobs: the SV modules, the ∀-N proofs, the nine
`agree.lean`, every `load_design_sv2` user except the three cv32e40p
`ingest.lean`) is green with every statement unchanged; all 28 reported
`#print axioms` are within [propext, Classical.choice, Quot.sound].
`docs_check` is clean and `divergence_register` reports OK.

**Gaps.**

1. `Constant:untyped-width` refuses every untyped constant built with
   `+ - * **`, INT class included (`localparam KM1 = K - 1`), at every
   point and whether or not its width is ever observed: rows
   `register_file_ff`, `fold_uovf` (four), `fold_uwid_n16`, and
   `fold_uwidp` at overridden points (the load gate refuses the design at
   its defaults first). Recorded over-refusals, not narrowed.
2. `InstanceSymbol:override-untyped-width` refuses such an override even
   where the child never observes the parameter's width.
3. The typedef and enum refusals hold at the default point too, where the
   envelope is exact.
4. An enum whose BASE width depends on the point (`typedef enum logic
   [N-1:0] {…}`) is not refused. Its members materialize at the point's
   base width, while the value tier's tree carries the default point's
   conversions; the cross-check reports the tree difference as a
   default-point fold, so no row can claim it. On a first `fold_enf` the
   values equalled Icarus at `N = 3, 4, 16`; no wrong value was found.
5. Two default-point widths in the value tier are read without a measured
   shape reaching them: `instExpr2`'s `resize` fallback to the envelope's
   width when neither a context nor the operand's width is known, and the
   `Squash2` self width in `selfWidth2`/`divOperandWidth2`. The `Squash2`
   node itself is refused, and it appears only at assignment roots.
6. An enum-typed parameter is read as an `int` (`declConstType`); its
   member default does not evaluate (enums bind after parameters), so the
   load gate refuses such a design, but `instantiate2` at explicit
   arguments would type it as an `int`. Not measured.
7. The `**` width model is an over-approximation from five measured
   shapes; Icarus's rule is base- and value-dependent.
8. The before-values of `fold_uwid`, `fold_uwidp` and `fold_uwint` were not
   re-run on a round 5 Lean build: for `vs_uw`/`vs_up` the verifier's logs
   show the model following Yosys, and for the INT class the value tier's
   32-bit `paramNWidth` gives Yosys's reading by construction.
9. svGolf (a separate lake project) was not rebuilt; the three cv32e40p
   `ingest.lean` files import the umbrella `LeanModels` and were not built.

## Unsized x/z literals at every point (round 5 repair, Lane A, refusal-only) — 2026-10-29

This entry closes the four findings of the verifier of the round-5 INIT
repair under the round 5 rule: refusal-only and monotone, no shape loud at
2e8c8b28 or in the round-5 tree admitted, and a class refused at one choke
point rather than shape by shape. Every change is in the extractor's
symbolic mode (additive; no M0 path, no Lean file). Repros: the verifier's
`gaps5/vinitA/d/` (`vp1`–`vp9`, `ex/ex3`), with its Icarus and Yosys
netlist traces in `o1`–`o5`; this round's probes, traces and logs:
`/private/tmp/claude-501/-Users-ahle-repos-lean-surfaces/ef50039c-ca19-4962-8585-1ff4626e9462/scratchpad/gaps5/init2/`.

**(1) Blocker: x/z literals fixed at the default point.** The envelope of a
family holds slang's binding at the DEFAULT point, and the round-4/5 hook
(`_sym_unsized_xz_widening`) saw only a widening visible there. A literal
of exactly the default context width carries no conversion, so a 32-bit
`Literal` reached Lean, which zero-extended it at every wider point; a
narrower default context folded the literal to a default-width `Literal`.
The envelopes were identical at 2e8c8b28, in round 4 and in round 5.

- `assign y1 = 'hx0` into `[N-1:0]`, `N = 32` by default (`vp3`): at `N =
  40` the model gave 8 zeros, 28 x, `0000`; Icarus 12.0 and the Yosys 0.53
  netlist give 36 x then `0000` (FAIL at `N` = 33, 40, 64).
- The child form (`vp4`): a non-parametric top instantiates a child with a
  32-bit default at `W = 40`. Wrong against both tools, with no cross-check
  for the shape: silent in `name.sem`.
- The `case` item `'hz1` over `[N-1:0] b` (`vp9`): at `N = 40`, `b` = 36 z
  then `0001`, the model gave 2, both tools 1.
- A default of `N = 8` (`vp6`) folded `'hx0` to `xxxx0000`, and the sized
  `12'hxF0` to `11110000` (`vp8`). The cross-check reports the silent fold
  (`vp6` at `N` = 31, 32; `vp8` at 12, 32, 33, 40, 64), and `vp6`'s rows
  FAIL against Icarus from `N = 33`. This round's probe `ov2`
  adds `default: y = 'bx` and `'bz` at `N = 8`: FAIL against Icarus at every
  `N` from 15 (at `N = 16`, `y2` is 8 zeros then 8 z, both tools 16 z).

The fix is ONE choke point, `_sym_xz_literal_scan`: a walk of every
converted module's bound tree (instance bodies excluded, port actuals
included), its findings `Unsupported` entries in the module's `others`, so
the design is loud. In a scope whose context widths differ between points
(a module with an overridable parameter, top or definition; a generate-for
body) every unsized x/z-top literal is `IntegerLiteral:unsized-xz-
parametric`, widened at the default point or not, and every x/z-bearing
literal under an implicit conversion that changes its width is
`ConversionExpression:xz-literal-parametric`. The literal of a declaration
initializer that `_sym_decl_init` decides from the literal itself (the
round-4 `Fill`/`Int`/fixed-width table) is the one exception
(`_sym_mark_decl_literal`). Fixtures and refusal rows: `ux_pdep`,
`ux_pdep_child`, `ux_pdep_narrow`, `ux_pdep_sized`, `ux_pdep_case`,
`ux_pdep_fill`, with the verifier's points.

**(2) Major: port actuals at another point.** `PortConnection:unsized-xz`
fired only where the port was wider than the literal at the BOUND point.
`vp1` (`W = N`, 32 by default) was admitted at `N` = 33, 40, 64 with
Icarus's zero padding (8 zeros, 28 x, `0000` at `N = 40`) against the
netlist's 36 x then `0000` (and Xcelium's): rows PASS with "xcheck
UNCONFIRMED, simulator-verified". `vp2` (a generate-for bound at `g = 0`)
did the same at `g = 1` with no cross-check, and `vp7` (`N = 8` by default)
was folded to the bound port width, wrong against both tools. `_sym_port_conn`
now refuses any input actual HOLDING an unsized x/z-top literal, at any
port width (`_sym_contains_unsized_xz`). Fixtures and refusal rows:
`pa_unsized_xz_p`, `pa_unsized_xz_g`, `pa_unsized_xz_n`.

**(3) Major: `$unsigned` of an unsized x/z literal.** `assign y1 =
$unsigned('hz1)` into 40 bits (`ex3`, one point) is 8 zeros, 28 z, `0001`
in Icarus 12.0 (the self-determined value zero-extended), as in the model
since 2e8c8b28, and 36 z then `0001` in the Yosys 0.53 netlist. The scan
refuses, in any scope, `$unsigned` of an expression holding an unsized
x/z-top literal whose result is widened (`CallExpression:unsized-xz-cast`;
fixture and row `ux_unsigned_cast`). `$signed('hz1)` widened agrees in both
tools (probe `ov3`) and is unchanged.

**(4) Minor: two policies in the docs.** Synthesis-side item 2 of
`docs/sv-oracle-disagreements.md` now says that it stands for sized x/z
`case` items and x/z constants under operators (the netlist reads them as
don't-cares; measured again on `ov1`, `ov3`, `ov4`), that the x/z
refusals of rounds 5 and this repair each have their own reason and are
supersets of that reading where they overlap, and that refusing the
general netlist reading is routed to the lead as one recorded decision.

**Corrections.** The round-5 entry's (1) and (5), the schema's round-4
"Unsized x/z literals in expressions" note and "Round 5 refusals", the
oracle doc's (A2) and port-width paragraph and the hook's docstring carry
CORRECTED notes; new: schema "Round 5 repair refusals", oracle (A5), (A6).

**Refusal sets.** Pre-repair against current, over every sv-0.2 envelope,
the round-4/5 INIT repro directories and the verifier's repros (435 tops):
nothing loud became admitted. Two tops (`pf`, `pfy`) changed kind only,
their nested `CallExpression`/`ConversionExpression:Explicit` refusals
inside port actuals now replaced by `PortConnection:unsized-xz` on the
same lines. 2e8c8b28 against current (439 tops): the admitted set is
round 5's (Lane A's converted and unsized initializers, Lane B's folds),
with no addition.

**Over-refusals (recorded gaps).**

1. `ux_pdep_fill`'s shape: `Fill` would be exact.
2. A sized x/z literal zero-extended into a `Resize` in a family (`ov1`,
   `12'hxF0` and `a ^ 4'bx1z0` into `[N-1:0]`, 16 by default). The
   pre-repair model equals Icarus at `N` = 1, 2, 3, 4, 7, 8, 15, 16, 31,
   32, 33, 63, 64, 65; the netlist differs only where x/z meets an
   operator.
3. An unsized x/z-top literal in a family position of fixed width, and an
   input port default of a family.
4. `$unsigned($signed('hz1))`, which agrees in both tools (`ov3`).
5. An actual into a fixed port of at most 32 bits (`.i('hx0)` into 32 or 8
   bits agrees in both tools, `ov4`).

**Verification.**

- **Build.** One slot build of the required list was green (74 jobs): the
  LeanModels.Sv modules, the ∀-N files, the `load_design_sv2` proof users
  and all nine sem2 `agree.lean`, with every statement unchanged. All 28
  `#print axioms` reports are within [propext, Classical.choice,
  Quot.sound].
- **Full `diff_test2 --sim iverilog`.** EXIT 0, 0 FAIL, 0 ERROR: 378
  verified, 21 declared, 155 loud (the 31 new refusal rows included), 24
  skipped, 23 unavailable; cross-check 263 row points agree, 2 unconfirmed
  (pre-existing). The 31 new rows were also run alone first: all refused
  with their kinds.
- **reext.** 265 same, 0 diff, 3 cv32e40p skipped. The envelopes this entry
  changes are the round-5 fixtures `pa_unsized_xz` (actuals refused whole)
  and `ux_expr_p` (scan findings added; its rows keep their kind), plus the
  ten new fixtures. The four committed probe sidecars regenerate
  byte-identically.
- **Extractor suite.** 1855 passed, 3 skipped (`test_sym_initializers.py`:
  12 new tests, 2 adjusted to the new refusals). The known-flaky
  `test_empty_associative_delete::test_symbolic_mode_stays_loud` fails in
  about one run in three under `-n 4`, with the pre-repair extractor too.
- **`cases2.json`.** 31 rows appended; no existing row changed.
- **docs_check.** Clean.

## Default-point folds, round 7 (Lane B repair, refusal-only: size casts, enum widths, left shifts, the `Squash2` own-width gate) — 2026-10-29

This entry closes the round 6 FOLDS verifier's five findings under the
round 5 rule: refusal-only and monotone. Every change is a new loud
refusal or the return of one; no computation changes, and no shape that
was loud at 2e8c8b28 or in the round 6 tree is admitted (round 6 had
admitted one; item 4 makes it loud again). `docs/sv-envelope-schema.md`,
"Default-point folds, round 7", is the reference;
`docs/sv-oracle-disagreements.md` items (14)–(16) record the new oracle
splits and items (5)–(6) of "Refused where the tools agree" the two
refusals where the tools agree. The verifier's repros `vw_szc2`, `vw_szo`,
`vw_enw`, `vw_shl`, `vw_shp`, `vw_sho` and `vw_sqd` are the fixtures
`fold_szc`, `fold_szo`, `fold_enw`, `fold_shl`, `fold_shp`, `fold_sho` and
`fold_sqd` (same bodies, renamed); `vw_szc3`'s shapes are unit tests in
`extractors/sv/test_sym_folds7.py`.

1. **A cast whose size depends on the point** (blocker; present at HEAD;
   the class round 6 was asked to search and missed; repros `vw_szc2`,
   `vw_szc3`, `vw_szo`). `localparam int X1 = M'(255)` and `X6 =
   M'(300)` were slang's default-point folds (-1 and 44 at `M = 8`) at
   every `M`: slang binds a size cast's size away, so the round 3
   `default-point-fold` guard, which looks for bound names, never saw `M`.
   Icarus 12.0, the Yosys 0.53 netlist and slang's elaboration at the
   point agree (255 and 300 at `M = 16`, 40, 64; X6 = -4 at `M = 4`, 0 at
   `M = 1`); the verifier's runs had the model at -1 and 44 at every
   point. The override form (`.W(M'(255))`, `.W(M'(300) + 1)` into an `int
   W`) folded the same way. Fix: in a family with more than one point,
   `_sym_conversion` refuses the M0 fold
   (`ConversionExpression:default-point-fold`) whenever any node of the
   operand has source syntax that depends on the point (new
   `_sym_bound_syntax_point_dependent`: `_sym_syntax_point_dependent`
   over each bound node's syntax, so a cast's size or type is seen). Every
   shape the verifier listed (`M'(1) << 3`, `signed'(M'(200))`,
   `$signed(M'(8'd200))`, `(M)'(255)`, `(M + 0)'(255)`, `logic [63:0] R9 =
   M'(255)`, `M'(200) + 1`) is refused (`test_sym_folds7.py`), and so are
   a parameter default `P = M'(255)`, a genvar bound `i < M'(2)` and a
   value-position `assign o = M'(255)` (scratch probe `p/szv.sv`); fixed
   casts and single-point modules keep the fold. Rows `fold_szc*`,
   `fold_szo*` (default, `M` = 1, 4, 16, 40, 64).
2. **Enum member values that depend on the base width** (blocker; present
   at HEAD; repro `vw_enw`). Two refusals at the member reference:
   * an initializer containing an unbased-unsized literal (`'0 '1 'x 'z`,
     `~'0`): `EnumValueSymbol:unsized-literal-member`, at every point and
     in every scope, package enums and single-point modules included.
     §5.7.1 and slang fill `'1` (EA = 15 at `N = 4`, the value the envelope
     carried); Icarus and the Yosys netlist both give EA = 1, the default
     point included (`{a, EA}` = 241 at `a = 15`; the model 255). At `N =
     8` the model's 15 matched no tool (slang 255, the tools 1). Rows
     `fold_enw*` (default, `N` = 2, 8, 33) and `fold_enu`.
   * a base type or dimension that depends on the point:
     `_sym_enum_values_point_dependent` now reads `baseType` and
     `dimensions` too (`EnumValueSymbol:default-point-value`). The
     envelope carries the default point's values and Lean truncates them
     to the point's width (`enumMemberVals`): `{SA = 9, SB = 2}` over
     `logic [N-1:0]` at `N = 3` is `EnumValueOutOfRange` in slang, an
     elaboration error in Icarus and SA = 1 in the Yosys netlist, the
     model's reading. Every member of such an enum is refused, including
     the FSM form `{T0, T1, T2}` where it fits (a recorded over-refusal).
     Rows `fold_enb*` (default, `N` = 3, 1, 8, 16).
3. **A left shift widens an untyped constant** (blocker; present at HEAD;
   repros `vw_shl`, `vw_shp`, `vw_sho`; the round 6 "stopped by a shift"
   was wrong for left shifts). Icarus widens `<<`/`<<<` by the amount
   where the left operand is or contains an unsized or INT-class operand
   (`$bits(1 << N)` = 32 + N; 2^40 at `N = 40` where Yosys gives 0); the
   model followed Yosys at every point (verifier runs: lean == yosys !=
   icarus on every mismatch). Fix: `PExpr.icarusWidens` counts
   `.shl`/`.ashl`/`.m0 (.shl _)`/`.m0 (.ashl _)` as widening (and, for
   completeness, the value-position spellings `.m0 (.pow ..)` as widening
   and `.m0 .div/.sdiv/.rem/.srem` as carrying), and `_sym_icarus_widens`
   counts `LogicalShiftLeft` and `ArithmeticShiftLeft`. `SB << 4` (a
   sized left operand, 8 bits in Icarus) is refused too — the `#guard`
   that pinned it at 240 now pins the refusal; a recorded over-refusal.
   Rows `fold_shl*` (`Constant:untyped-width`; default, `N` = 0, 1, 2, 3,
   33, 40, 64), `fold_shp*` (default, `N` = 1, 31, 33, 40), `fold_sho*`
   (`InstanceSymbol:override-untyped-width`; same points).
4. **The `Squash2` own-width gate** (major; a round 6 admission of a shape
   round 5 refused; repro `vw_sqd`). Round 6's `ctxPropagates (.squash2
   _ a) = a.ctxPropagates` let the context reach a squashed operand that
   divides by zero at its own width: `localparam shortint H1 = 4'd8 / (U
   + 1'b1)` at a 4-bit `U = 15` was `division by zero` in round 5 and 0 in
   round 6 (0 is also what slang, Icarus and the Yosys netlist give). The
   round 5 rule admits no loud shape, so the lead's option (b) is taken:
   `evalAt`'s `resize`, `signedResize` and `squash2` arms first evaluate a
   `Squash2` operand at its own width (the round 5 reading,
   `PExpr.isSquash2`) and propagate its error; the context value is
   returned only when that reading is defined. Where it is, nothing
   changes (rows `fold_sqd`, `_n2_u3`, `_n1_u1`, `_n4_u7`, `_n33_u5` run,
   slang, Icarus and the Yosys netlist agreeing three-way on H1, H2, H3);
   where it is not, the point is loud (`_n4_u15`, `_n7_u127`, `_n8_u255`;
   recorded over-refusals at the first two, where all three tools agree
   on H1 = 0, H2 = 9; at `N = 8, U = 255` the byte H2 splits, Icarus 0 and
   the Yosys netlist x). The round 6 report's `newly_admitted: None` was
   wrong; with this gate it is true.
5. **Over-claims corrected** with round 7 notes: "stopped by a shift" in
   the charter's round 6 item 4 (and the round 5 entry's item 6), the
   schema's round 6 and round 5 untyped bullets, oracle-disagreements items
   (11) and (12), and the docstrings of `PExpr.icarusWidens` and
   `PExpr.shiftBarriers`; the round 6 entry's "Nothing that was loud is
   admitted" and its item 1; the round 6 enum item. The round 6 report's
   sentence that the 235-row prefix of `cases2.json` from HEAD was
   unchanged was also wrong: HEAD row 63, `register_file_ff`, was one of
   its nine corrected rows (PASS → `Constant:untyped-width`).

**Before and after.** With this round's extractor hunks disabled (a scratch
copy) and the current Lean, the fixtures reproduce the verifier's values:
`fold_szc` at `M = 16` read X1 = -1 and X6 = 44 where both tools give 255
and 300, and `fold_szo` 45 where they give 301; `fold_enw` read EA = 15 at
the default where both tools give 1 (3 at `N = 2`); `fold_enu` 15 for 1;
`fold_sho` 0 where Icarus gives 2^33 at `N = 33`. The 2e8c8b28 extractor
emits the same default-point literals for `fold_szc` and `fold_szo`. After:
every one of these rows is refused with its kind.

**Verification.** Scratch (regenerated after the 2026-10-29 machine
restart cleared `/private/tmp`, including the round's first scratch
directory and the verifier's): `/private/tmp/claude-501/-Users-ahle-repos-lean-surfaces/ef50039c-ca19-4962-8585-1ff4626e9462/scratchpad/gaps5/folds4/`
(`o1/` Icarus and Yosys netlist traces of all 48 rows, `logs/`).

- **Build.** One slot build of the required list was green (75 jobs): the
  LeanModels.Sv modules, the ∀-N files, the `load_design_sv2` proof users,
  `clog2`/`unary_plus`/`multiplication` and all nine sem2 `agree.lean`,
  with every statement unchanged; it was repeated, green, after the last
  edit (a docstring note on `PExpr.shiftBarriers`, made while the
  differential run below used the oleans of the first build). All 28
  `#print axioms` reports are within [propext, Classical.choice,
  Quot.sound].
- **Oracles.** Icarus 12.0 and the Yosys 0.53 netlist agree on every cycle
  of `fold_szc*`, `fold_szo*`, `fold_enw*`, `fold_enu`, `fold_enb`,
  `_n8`, `_n16` and every `fold_sqd` point but `_n8_u255`; they split on
  every `fold_shl*`, `fold_shp*`, `fold_sho*` row and on `fold_sqd_n8_u255`
  (H2); Icarus refuses `fold_enb_n3` and `_n1`. slang's elaborated values
  agree three-way on every `fold_szc*` point and on every `fold_sqd` point
  but `_n8_u255`.
- **Full `diff_test2 --sim iverilog`.** 626 cases, EXIT 0, 0 FAIL, 0
  ERROR: 383 verified, 21 declared, 198 loud refusals, 24 skipped, 23
  unavailable backends; cross-check 267 row points agree, 2 unconfirmed
  (pre-existing).
- **reext.** 265 same, 0 diff, 3 cv32e40p skipped; the four committed probe
  sidecars and their envelopes regenerate byte-identically. The only new
  envelopes are the nine fixtures.
- **`cases2.json`.** 48 rows appended (578 → 626); no existing row changed
  in this round. Against 2e8c8b28 the 235-row prefix differs in
  `register_file_ff` only (round 6).
- **Extractor suite.** 1854 passed, 3 skipped, 1 failed: the known-flaky
  `test_empty_associative_delete::test_symbolic_mode_stays_loud` (alone it
  passed in 2 of 4 runs).

## Xcelium audit, round 6, lane A (refusal-only: partly out-of-range selects, net-to-net port width, wide bit-select index) — 2026-10-29

Thomas's policy for the 36 rows on which `docs/sv-xcelium-audit.md` found the
model differing from the pinned Xcelium 24.03-s004 traces: where the tools
split, or where the model would follow one oracle against the LRM, REFUSE
LOUDLY (Xcelium is the reference for ls-sv decisions but is not infallible:
where it departs from explicit IEEE 1800-2023 text we neither follow it nor
pick silently). The round's rule is refusal-only: a change may add a loud
refusal, add or correct a declaration or its documentation, and nothing else;
no loud shape became admitted and no value the model computes changed except by
becoming a refusal. Lane A's three clusters (decisions of the lead, not
re-litigated here):

1. **P1/P3/DX1 — constant part selects PARTLY out of range** (`Param2.lean`,
   `RangeGuard2.lean`). `arrayPartRead`'s final overhang branch (the in-range
   window concatenated with x fill) is `Expr2.unsupported
   "ArraySel:partial-overhang"`; `arrayPartTarget`'s msb-overhang clip and its
   lsb-overhang sink-leaf branches are one `Except.error` beginning with the same tag
   (`partOverhangMsg`). The wholly-outside branches (x read, no-op write), the
   in-range branches, single-bit selects and `ArraySel:index-range` are
   unchanged. The legacy `partSel` arms of `instExpr2`/`instLhs2` lower to a
   constant `.slice` that `LVec.extract` x-pads silently: they cannot change
   (the lowering lemmas and the ∀-N examples pin `name.sem`), so the same overhang
   is checked beside `name.sem` in the select guard family
   (`Design2.firstSliceViolation`, `Select:partial-overhang`, run by
   `load_design_sv2` at the defaults and every probed point, by
   `probeCheckString` and by `harness/sv/runner2.lean` through the new
   `PDesign.selectGuardReport`, which returns the first of three kinds;
   `legacyRangeReport` is untouched). No recorded theorem needed the refused
   branches: `arrayPartRead_of_inRange`, `arrayPartTarget_of_inRange`, the
   `…_desc0` window lemmas, `CombViewThm` and `svgolf/tasks/mul` use the in-range
   statements only; `arrayFlatWidth` is kept (no longer used by the target,
   named by `sv2_inst_simp`). Pinned `#guard`s that asserted the clip/sink
   values are now refusal guards (Param2: the `m[0][4:2]`/`v[6 +: 4]`/`v[-2 +: 4]`
   family, `pCtx` at `N = 8`, `pDynPart`'s lsb-overhanging write moved to an
   in-range one with the old shape kept as `pDynPartOv`; partsel/gen.lean: all five
   differential points are loud because `ov_hi = a[N*W-2 +: 4]` leaves the
   vector at every point, `ov_lo`/`w_hi`/`w_lo` guards state loud-vs-window).
   Fixtures `overhang_read`, `overhang_write`, `overhang_legacy` (rows at the
   overhanging point, an in-range control and a wholly-outside control).
   **33 existing rows flipped to loud-refusal rows** (the audit's 30 P1 rows,
   `array_oob_lsbwrite`, and the two `ctx_width` rows that had matched only
   because the x bit collapsed a sum), each with a `measured` field. A RUN-TIME
   base (cluster P2) cannot be refused statically and is the lead's declaration.
2. **H1 — a NET formal fed by a bare, narrower NET actual** (extractor
   `_sym_net_bound_actual`, `Ingest2.lean`, `Hier2.lean`). Xcelium binds the nets bit
   for bit (the formal's high bits z, `CUVMPW`); the model, Icarus, Verilator,
   Yosys and slang zero-extend. The extractor marks the shape on the
   CONNECTED input (`"net": true`, until now only on an unconnected one),
   `connProcs` is `PortConn:net-width` where the actual is narrower than the port
   at the instance's own point. Variable actuals (a body `logic`, and an
   `output logic` / `output reg` / `output var logic` port: an output with an
   explicit data type is a VARIABLE, IEEE 1800-2023 23.2.2.3 — see the repair
   below, the first version marked those as nets), part-/bit-selects, constants,
   expressions, `var` and 2-state formals and equal-or-wider actuals are
   unchanged. The mark is not emitted when both declared widths are literal and
   the formal is not wider, so only five existing envelopes changed
   (`hier_clk`, `hier_nested`, `hier_params`, `hier_width`, `int_const_hier`, one
   `"net": true` per marked connection); every other committed sv-0.2 envelope
   re-extracts byte-identically (reext at the end of the lane: 289 same, 0 diff,
   the three cv32e40p sources off-machine skipped). Rows `hier_width`, `hier_width_n2`, `hier_width_n6`
   flipped; fixtures `net_width_min` (refused) and `net_width_ok` (variable actual
   and expression, admitted). Hand-built `#guard` designs in `Hier2.lean` that set
   `net := true` on a connected input (a no-op until now) were set to `false`.
3. **T1 — a bit-select index wider than 32 bits** (extractor
   `_sym_wide_index_refusal`, `RangeGuard2.lean`). The model takes the index whole
   (the LRM text, Yosys `prep; eval`); Xcelium (BIGWBS), Icarus and Verilator
   truncate it to 32 bits, so the old declaration `iverilog-wide-index-truncation`
   ("Icarus alone") was contradicted. Run-time index above 32 bits: extractor
   `ElementSelectExpression:wide-index` where already wide at the default point
   (in a READ; in a WRITE target the Unsupported node that reaches the envelope is
   the assignment's, `AssignmentExpression:target`, because a refused select leaves
   no usable target — fixture `wide_index_wr`, row `wide_index_wr`),
   `Select:wide-index` per point (`PDesign.wideIndexViolation`, `selfWidth2`) in the guard
   family; a constant of 2^32 or more likewise. The model does not truncate.
   Rows `fold_pcase_n31`, `fold_pcase_n40`, `fold_pcase_n40_pm1`,
   `fold_pcase_n40_p5`, `fold_pcase_wide` flipped (`fold_rself_n40` stays);
   the declaration text is corrected (and the declaration since retired with the
   other refused rows). Fixtures `wide_index` (per point), `wide_index_lit` and
   `wide_index_const` (the extractor's refusals).

`harness/sv/runner2.lean` now also names the first loud node with its text
(`Design2.firstLoud`), since `run2` names the node's kind only and a refused
assignment TARGET is `unsupported statement 'AssignL'` with the tag in its text.

Recorded gaps: the net-to-net output twin and a part-/bit-select of a net
actual (Xcelium z-fills those; not refused); a wide index in a generate-local
declaration (not in the point's width table); `ArraySel` constants of 2^32 or
more are not seen by the guard (the extractor refuses the literal ones); the
audit's 428-row accounting is a snapshot and is not rewritten (pinned golden
entries of the 38 flipped rows stay as evidence).

Documentation: `docs/sv-oracle-disagreements.md` ("Linearized packed-array
indices", "Select indices wider than 32 bits", "Port connection width context",
(R6a)), `docs/sv-envelope-schema.md`, the Param2/Hier2/RangeGuard2 docstrings.

### Lane A repair (verifier round, refusal-only) — 2026-10-29

Three findings of the verification of lane A, all closed under the same
refusal-only rule (no loud shape became admitted relative to the committed
tree; the changes narrow an over-refusal the lane had introduced and correct text).

1. **MAJOR — the net-to-net mark was too broad** (extractor `_sym_symbol_net_kind`).
   The helper took every Variable port symbol with a `VariablePortHeader` and no
   `var` for a net. That is right for `input logic [1:0] s` (IEEE 1800-2023
   23.2.2.3: an input port without `var` is a net) and WRONG for `output logic`,
   `output reg` and the non-ANSI `output reg [1:0] o;`: an output declared with an
   explicit data type is a VARIABLE, and slang reports it with the same header and
   the same empty `var` keyword. A narrower `output logic/reg` port of the
   instantiating module feeding a wider input formal of a child was therefore
   marked `net: true` and refused as `PortConn:net-width`, although all four tools
   zero-extend a variable actual (the pre-change model admitted it; the verifier's
   probes `nw_outreg`, `nw_var_out`). The Variable branch now requires the header's
   direction token to be `input` or `inout`; an implicit-type output
   (`output [1:0] o`) and `output wire` are slang `Net` symbols and stay marked.
   Measured on Xcelium 24.03-s004 (vip-ng, refsim; `gaps6/r3/xcel`): an
   `output logic`, an `output reg` and an `output var logic` actual into the
   wider net formal give exactly the Icarus 12.0 trace in all 6 cycles (zero-extended,
   CUVMPW warned, no z), one bit wide as well (`net_width_outvar1`); an `output wire`
   and an implicit-type `output` z-fill (`pw = zzzz01` for two bits, `zzz0` for one),
   like an input net. **Measured finding on the way:** net OUTPUT actuals never reach
   `PortConn:net-width` today. The symbolic tier cannot recover the packed dimensions of
   a NET declaration (`wire [1:0]`, even `input wire [1:0]`), so a VECTOR `output wire`
   actual is refused earlier by the cross-check (`unrecoverable packed dimensions`, row
   `net_width_outwire`), and a SCALAR one by the model itself (`assign target 'ow'
   undeclared`, row `net_width_outwire1`: the tier does not declare a net output port).
   `PortConn:net-width` is reached through slang-Variable ports (`input logic`), which
   is the lane's shape. The extractor's mark on an output net is kept (it is the intended
   guard if net outputs become admissible, and unit-tested), and the two rows pin the
   earlier refusals and carry the Xcelium z-fill evidence; the verifier's finding itself
   (variable outputs over-refused) is pinned at the model level by the controls.
   Fixtures `net_width_outvar` and `net_width_outvar1` (controls: simulated,
   `XREF-MATCH`, pinned), `net_width_outwire1` and `net_width_outwire` (refused
   earlier). Extractor tests: `NetBoundOutputActual` (10 tests, 4 of which fail
   against the previous logic; one also pins that the direction is read from the
   token's own text, since `str(token)` carries the comments before it — a `// clk`
   line above an `input` port would otherwise hide it). Re-extraction of every
   sv-0.2 envelope that can be re-extracted: 301 same (the 295 earlier ones and the
   six new fixtures), 0 diff, 0 fail (3 skipped: the cv32e40p sources); the five
   envelopes lane A changed re-extract identically, i.e. none of their `net` marks
   was an output-variable mark.
2. **MINOR — `Select:wide-index` over-approximated on dead generate code**
   (`RangeGuard2.lean`). `GenItem.bitIdxs` walked both arms of every `genIf` and
   every `genFor` body, instantiated or not, and judged the index at the module's
   width table (probe `wi_dead2`: a wide `v[a]` in the `N == 4` arm refused at
   `N = 40`, where that arm is not instantiated; the pre-change model admitted it,
   and Xcelium, Icarus and the model agree on all cycles). It now walks what the
   point INSTANTIATES (`GenItem.liveBitIdxs` / `PDesign.liveBitIdxs`, mirroring
   `GenItem.expandH`: the taken `genIf` arm, the iterations `genvarSeq` yields,
   each under its genvar binding; a condition or loop header that does not evaluate
   leaves both arms or the body walked, as before). `PDesign.wideIndexViolation`
   and `PDesign.selectGuard` take the generate fuel `F`; no other caller exists.
   `#guard`s `pDeadArm` (arm dead / live / narrow) and `pLoopIdx` (a zero-iteration
   loop is not judged, one iteration is). Fixture `wide_index_dead`, rows
   `wide_index_dead_n4` and `wide_index_dead_n40` (admitted, pinned, Xcelium =
   Icarus; no BIGWBS because the truncating arm is not elaborated) and
   `wide_index_dead_n40_live` (the same select instantiated: `Select:wide-index`).
   The extractor's own `ElementSelectExpression:wide-index` node was already lazy
   (an `Unsupported` node inside a dead arm is only reached if the arm is
   expanded).
3. **MINOR — wording.** The write tag is `AssignmentExpression:target` (above);
   fixture and row `wide_index_wr` pin it at an already-wide default point
   (Xcelium writes at the index truncated to 32 bits, Icarus drops the write).
   Packed-array element selects with a wide index are refused by the extractor
   (`ElementSelectExpression:wide-index`, probes `wi_pk`, `wi_pk2`). The recorded
   gap "unpacked-array element indices are not covered" was too strong: a run-time
   unpacked-array element index that the extractor admits is judged by the Lean
   guard per point (the verifier's probe `wi_arr` at `N = 4`: `Select:wide-index`,
   a 35-bit index; the extractor refuses most such accesses first, with another
   tag). What stays uncovered is the shift count wider than 32 bits (Xcelium
   truncates it silently, nothing refuses it); the register's hole entry says so.

Build and checks: the lane-A build list (`LeanModels.Sv.{Ingest2, Param, Param2,
RangeGuard2, Gen2, Hier2, Hier2Gen, CombGuard2, CombGuard2Sound, Comb2Example,
Comb2ConcatExample, Comb2Proc, Comb2ProcExample, Mono2, SelfCheck, Tests,
CombAlias2, CombAlias2Sound, CombAlias2Example}`) rebuilds green; no recorded
theorem depended on either change (the wide-index guard is a CHECK beside the
semantic family, see the `RangeGuard2.lean` header).

## Xcelium audit, round 6, lane B (the `always_comb` alias guard, refusal-only) — 2026-10-29

Decision (6) of the lead on the Xcelium audit's cluster D4: an `always_comb`
that reads a continuous copy of a variable it writes is REFUSED where the
event-driven tools split. The rule, the mechanism and the rows are in
`docs/sv-oracle-disagreements.md` ("Icarus propagates a copy inside the
block's own run: the alias rows are REFUSED") and `docs/sv-envelope-schema.md`
(the `AlwaysComb:self-read` paragraph); this entry records what was built and
what it does not do. The round's rule held: the change adds a loud refusal and
corrects documentation; no shape that was loud became admitted, and no value
the model computes changed except by becoming a refusal.

**The guard** (`LeanModels/Sv/CombAlias2.lean`, new). `Design2.aliasGuard`
replaces each `Process2.alwaysComb` whose body `Stmt2.aliasViol` refuses by
`Process2.unsupported "AlwaysComb:alias-read" msg`; every other process is
untouched, and the name, the declarations and the process order are kept.
`Stmt2.aliasViol` is `Stmt2.combViol` (the self-read guard) with the
written-after set replaced by its FAN-OUT through the design's continuous
assignments: `fanOut fl A` is the write windows of every `Process2.assign`
reachable from the windows `A` by at least one hop (`Process2.aflow`: an
assign reads its right-hand side and its target's index expressions and may
write its target), compared with the reads by the self-read guard's own
`readsViol` (`Expr2.rdW`, `Stmt2.mayW`: the same bit granularity — constant
slices exact, a run-time index covers its signal). The fan-out is transitive
(a chain of assigns) and keyed on the dependency path, NOT the functor kind
(`assign w = ~t` is refused although every tool agrees on it), and after
`Hier2.lean`'s flattening the assigns include the port connections, so a port
loop (a child's input and output tied to one parent variable) and a copy made
BY a child instance (`acg_alias_thru`: three assignments, none in the parent's
module) exist only at that level. The message names the module, the copy (and
its instance and flattened name when it is a flattened instance's signal), the
bits, the variable the block writes later, and cites IEEE 1800-2023
§9.2.2.2.1 and §4.7/§4.8. Not refused (every tool agrees): write-then-read
(A6), a SEPARATE `always_comb` copy (A5), a copy of a variable the block does
not write, a copy of bits the block does not write.

**Where it runs.** BESIDE `name.sem`, like `RangeGuard2.lean`: the lemmas
`PDesign.instantiate2_eq`, `assemble2_processes`, `instantiateG2_of_ok`,
`instantiateGD2_of_ok`, `instantiateGD2_eq_driverGuard`, `driverGuard_of_ok`,
`instantiateH_of_rec`, the ∀-N proofs of `ripple_add`, `mul2d`, `partsel`,
`ripple_fa` and `CombViewMain.lean` (which unfolds `instantiateGD2`) are
stated for the unguarded family, so a guard inside `instantiate2` /
`instantiateG2` / `instantiateGD2` would falsify them. It runs on the
INSTANTIATED design (the flattened one for a hierarchy):
`load_design_sv2` at the defaults (`Ingest2.lean`, kind beside
`AlwaysComb:self-read` in the refusal loop) and at every probed point
(`Envelope2.aliasAtPoints`, `probeCheckString`), `harness/sv/runner2.lean` at
each row's point, `PDesign.aliasReport` for any other tool. `Process2.inInstance`
is NOT extended: the guard runs once on the flat design, where the child's
processes were already renamed, and the message names the instance from the
flattened signal (`u.w` -> instance `u`); a per-level guard could not see a
port loop or a copy made by a sibling. RECORDED RESTRICTION: `name.sem N` at a
parameter point other than the defaults and the probed ones does not carry the
refusal (the self-read guard, which lives in `instProcess2`, does).

**Proof** (`CombAlias2Sound.lean`, `CombAlias2Example.lean`; new, standard
axioms only, every `#print axioms` pinned with `#guard_msgs`). Proved:
`fanOut_closed` (the fan-out is closed under the flows) and `Down.mem_fanOut`
(every downstream bit is in it); `Stmt2.aliasViol_epaths` and
`Stmt2.aliasAdmits_epaths` (path safety: on EVERY control path of an admitted
body, no read touches a bit downstream of a bit the path writes at or after
the read — exactly the refusal rule); `Design2.aliasGuard_idem`,
`aliasGuard_sound`, `aliasGuard_of_noComb` (`ripple_add`, `mul2d`, `ripple_fa`),
`aliasGuard_of_noAssign` and `aliasGuard_of_admits`; and for the proof API's
designs `fa/mux/latch/dec_aliasGuard` and `as_aliasGuard N` for EVERY width,
plus the pinned shapes (`alias_guard`, `wr_admits`, `copy_aliasGuard`,
`alias_refused`). The `agree.lean` files of the `always_comb` fixtures
(`addsub_comb`, `fa_comb_proc`, `latch_comb`, `mux4_case`, `onehot_dec`)
`#guard` that the guard leaves their instantiated designs unchanged. NOT
proved: that a simulator which applies the copy inside the block's run reads
the same values as one that defers it (`Sem2.lean` has no intra-block
propagation semantics to state it against); the justification stays the
measured mechanism. Nothing recorded was edited: no `CombGuard2Sound.lean`,
`Comb2ProcExample.lean`, `Hier2.lean` or ∀-N statement changed for this guard.

**Rows** (`harness/sv/cases2.json`). `acg_alias_assign` and `acg_alias_port`
flipped from declared-Icarus-departure rows to loud-refusal rows
(`"refusal": "AlwaysComb:alias-read"`, each with a `measured` field); their
declarations `iverilog-comb-assign-alias-sensitivity` and
`iverilog-comb-port-loop-sensitivity` are retired (both named this guard as a
retirement condition; recorded in "Declarations retired in round 6"). New
refusal rows: `acg_alias_wire` (a net), `acg_alias_chain` (transitive),
`acg_alias_not` (`~t`: every tool agrees, refused all the same),
`acg_alias_bits` (a bit the block writes is among the copy's bits),
`acg_alias_hier` (the alias inside an instance), `acg_alias_thru` (the copy
made by a child, through its ports). New admitted rows (Icarus = Xcelium =
model, the Xcelium traces pinned in `harness/sv/xcelium_golden.json`):
`acg_alias_wr` (write, then read), `acg_alias_copy` (a separate `always_comb`),
`acg_alias_far` (a copy of what the block does not write),
`acg_alias_bits_ok` (the copy is of bits the block does not write),
`acg_alias_port_wr` and `acg_alias_hier_ok` (write-then-read through a port
loop and inside an instance). `acg_xproc_bits` stays a declared Icarus
departure with tightened text (§6.5; the Icarus gap is WHOLE-VECTOR reads only:
`y = t` and `y = t[1:0]` stale, `t[0]` and `{t[1], t[0]}` fine). Fixtures and
envelopes under `Examples/system-verilog/sem2/acg_alias_*`; the sources of
`acg_alias_assign`/`acg_alias_port` had their header comments rewritten and
their envelopes regenerated (byte-identical to a fresh extraction).

**Verification** (2026-10-29; every Lean job through the machine's one Lean
slot). *Builds:* `lake build` of `LeanModels.Sv.{CombAlias2, CombAlias2Sound,
CombAlias2Example, Ingest2, Param, Param2, RangeGuard2, Gen2, Hier2, Hier2Gen,
CombGuard2, CombGuard2Sound, Comb2Example, Comb2ConcatExample, Comb2Proc,
Comb2ProcExample, Mono2, SelfCheck, Tests}` (37 jobs) and of the ∀-N proofs
(`ripple_add/{gen,proof}`, `mul2d/gen`, `ripple_fa/gen`, `partsel/gen`) with the
nine `sem2` `agree.lean` files (50 jobs): green; the three new files were also
elaborated directly with `lake env lean` (exit 0, no output: every `#guard` and
every `#guard_msgs` axiom pin holds). Every `#print axioms` of the new
theorems is within `[propext, Classical.choice, Quot.sound]` (the pins:
`fanOut_closed`, `fanAux_closed`, `Down.mem_fanOut`, `aliasViol_epaths`,
`aliasAdmits_epaths`, `aliasGuard_of_noComb`, `aliasGuard_of_admits`,
`aliasGuard_of_noAssign`, `aliasFlows_nil_of_noAssign`, `aliasGuard_sound`,
`aliasGuard_idem`, `as_aliasGuard`, `fa/mux/latch/dec/copy_aliasGuard`,
`alias_guard`, `alias_selfread_admits`, `wr_admits`, `alias_refused`,
`wr_aliasGuard`); no `sorry`, `native_decide`, `bv_decide`, axiom,
`implemented_by` or `extern`. *Census* (one Lean process per sweep): of the 494
sv-0.2 envelopes in the tree (294 in `Examples/system-verilog`, 200 of
svGolf's) the guard refuses exactly the six alias fixtures that existed at the
sweep (150 probe sidecars, every probed point: none); of the 676 rows of
`cases2.json` at their own parameter points exactly the seven
`AlwaysComb:alias-read` rows (662 pass, 7 points that cannot be built are the
`fold_shp*`/`fold_uwidp*` refusal rows). *Differential*
(`diff_test2.py --sim iverilog --golden` over the 44 rows that matter — every
`acg_*` and `rbw_*` row, the `always_comb` designs `fa_comb_proc`, `mux4_case`,
`latch_comb`, `onehot_dec`, `addsub_comb*` and `t2_*` — run before and after the
final rebuild): 24 verified against Icarus, 1 skipped (`t2_ci`), 1 declared
(`acg_xproc_bits`, CHECKED with the tightened text and its hashes), 18 loud
refusals (the seven alias rows, `acg_alias_wire` `NetSymbol:net-z`, the nine
`AlwaysComb:self-read`/`AssignmentExpression:compound` rows and `rbw_child`),
0 FAIL, 0 ERROR; against the pinned Xcelium traces 26 `XREF-MATCH`, 0
`XREF-DIFF`/`STALE`/`NONE` once the six new admitted rows were pinned (before
that, 6 `XREF-NONE`). The load gate: `load_design_sv2` on `acg_alias_assign`,
`acg_alias_port` and `acg_alias_thru` is `REFUSED — at the defaults, always_comb
block of module … reads bits [1:0] of … a continuous copy …` and on
`acg_alias_wr` and `acg_alias_hier_ok` loads (and `aliasGuard` is the identity
on `acg_alias_wr.sem`). New unit tests: `harness/sv/test_alias_battery.py` (8
tests, wired into `tools/ci.sh`: fixtures fresh, refused rows loud with a
`measured` field, `acg_alias_wire` refused by `NetSymbol:net-z`, admitted rows
undeclared and Xcelium-pinned, the two declarations gone and the third kept,
the documentation naming everything); `test_oracle_disagreements.py` (44),
`test_xcelium_golden.py` (20), `test_xcelium_compare.py` (20),
`test_oracle_admission.py`, `gen_sv_refusals.py --check` and `docs_check.py`
unchanged green.

**A fixture that did not test what it claimed.** The first draft of the battery
carried `acg_alias_wire` (`wire w; assign w = t;`) as an alias-guard refusal
row. It was never exercised before this verification: the extractor already
refuses every internal `wire` (`NetSymbol:net-z`, 2026-10-28), so the alias guard
never sees it and the row's expected kind was wrong (the harness would have
reported "refused, but not for AlwaysComb:alias-read"). The row now pins the
refusal that actually happens, its text says so, and the nets the tier admits —
input ports — are covered by the port-loop rows.

**Xcelium evidence** (vip-ng, only through `refsim`, one run at a time, own
directory `/tmp/ta-r6/…`): the 13 fixtures of the original battery were run in
the first half of the lane; `acg_alias_thru` (a new minimal repro) was run once
more (Xcelium `y = a` on all 8 cycles, Icarus one change behind); the six
admitted rows were pinned with `xcelium_batch.py prepare/run` into a scratch
copy of the golden file and merged into `harness/sv/xcelium_golden.json` (six
entries added, nothing else touched; 465 rows pinned).

**Recorded gaps.** (1) The restriction above: `name.sem N` at an arbitrary
point is unguarded for this kind; a ∀-N theorem about a design with
`always_comb` and `assign`s together would have to discharge the guard itself
(`aliasGuard_of_admits`). (2) Conditions are independent in the walk, as in the
self-read guard: a body whose only violating path is statically infeasible is
refused too (conservative). (3) Only `Process2.alwaysComb` is checked; the
other comb-phase kinds do not exist in the tier (`always @*`, `always_latch`
are refused by the extractor). (4) The message says `module '<top>'` and names
the instance only through the flattened signal; it does not name the child
module's own name. (5) The class where Icarus drops bits of a partly written
variable (`acg_xproc_bits` and its kin) is not an alias and is not refused.

## Xcelium audit, round 6, lane C (declarations, rows, pins, books) — 2026-10-29

Lane C of the round that acted on `docs/sv-xcelium-audit.md` (the other two lanes are the
refusals: lane A, the constant part-selects, the net-to-net port width and the wide bit-select
index; lane B, the alias guard `AlwaysComb:alias-read`). The round's rule is refusal-only: a
change may add a loud refusal or add or correct a declared departure or a document; no loud
shape became admitted and no value the model computes changed except by becoming a refusal.
(The earlier "round 6 / round 7 folds" entries of this file belong to the previous folds
workflow; this is the Xcelium-driven round.) Decisions of the lead, not re-litigated: (2) the
run-time-base partial part-select is DECLARED, (3) the pin stays on Xcelium's default flags and
`-ii_val` is recorded, (7) the D1, D2, D3 and DX2 declarations stay with upgraded texts, (8) the
false header comments are corrected.

1. **A declaration can name Xcelium** (`harness/sv/oracle_disagreements.py`, `diff_test2.py`,
   `xcelium_golden.py`, `xcelium_compare.py`). `oracle_disagreement.sim` is `"iverilog"` or
   `"xcelium"` (the harness calls the same simulator `xrun`; the checker accepts either name).
   Checked LIVE exactly like an Icarus declaration (a changed input or trace, or an agreement,
   is a hard failure) and against the PIN in `diff_test2.py --golden`, where the pin plays the
   simulator: `golden_disagreement`, `Xref.check(..., declaration)`, the new status
   `XREF-DECLARED` (counted apart from `XREF-MATCH` and `XREF-DIFF`; never a match; exit code
   unaffected, also under `--golden-strict`), and a declared departure that is resolved or has
   changed FAILS the run. On a stale, absent or failed pin the input bindings are still checked
   (`check_declaration_bindings`). In an Icarus-only run the row prints
   `xcelium:DECLARED DEPARTURE (id; checked by --golden, not here)` beside its Icarus match.
   `xcelium_compare.py` gained the verdicts `DECLARED-XCELIUM:holds|resolved|changed`.
   `harness/sv/declare_disagreement.py` writes a declaration (the digest recipe is the
   checker's own, `binding_digests`, factored out of `_check_bindings`; a test reproduces three
   committed declarations from their inputs bit for bit). One declaration per row. 24 new tests
   (18 in `test_oracle_disagreements.py`, 4 in `test_xcelium_golden.py`, 2 in
   `test_xcelium_compare.py`; one more was renamed).
2. **The P2 declaration** (`xcelium-runtime-partial-part-select-all-x`): a part-select with a
   RUN-TIME base that is partly out of range. Xcelium returns all x for the whole select;
   IEEE 1800-2023 11.5.1, the model, Icarus and Yosys read x in the out-of-range bits only. Six
   rows, all verified by an independent LRM oracle (the model equals it on every cell; Xcelium
   is all x on every partly-out cell and equals it on every other cell: 22 cells with 6
   partial on each `partsel_dyn*` row, 55 with 15 on `dyn32_part`): `partsel_dyn`,
   `partsel_dyn_n2_w5`, `partsel_dyn_n6_w2`, `partsel_dyn_n5_w1`, `partsel_dyn_n1_w4`
   (fixture `sem2/partsel_dyn`, the part of `partsel` that stays admitted) and `dyn32_part`
   (fixture `dyn32`, a stimulus that keeps every base non-negative). Row `dyn32` is NOT
   declared: 8 of its 22 differing cells are the model's two's-complement reading of a 32-bit
   unsigned base, which Xcelium reads unsigned (an open item, audit 6.4). svGolf's
   `fourstate` stage refuses run-time selects that can leave their range, so a scored design
   never reaches the shape.
3. **Row splits** (the fixtures keep the coverage of the admitted halves; every split row is
   model = Icarus = Xcelium except where a declaration says otherwise, checked row by row):
   `array_oob_asc` (the one confirmed shape of `array_oob_part`, `q[0][4]`: a declared Icarus
   disagreement, Xcelium = model; the other outputs of `array_oob_part` are all partial
   overhangs, so there is no in-range read to keep), `label_kminus_q` and `label_kminus_p*`,
   `hier_width_ok*` (u4 fed by a variable copy, which every tool zero-extends: the other four
   instances keep their coverage), `param_types_ok*` (the 8 rows without the two selects that
   overhang), `partsel_dyn*` and `dyn32_part` above. The declarations of the four rows lane A
   made refuse (`array_oob_part`, `array_oob_lsbwrite`, `label_kminus_w1`, `fold_pcase_wide`)
   are retired from the file, and with lane B's two (`acg_alias_assign`, `acg_alias_port`)
   recorded in `docs/sv-oracle-disagreements.md` ("Declarations retired in round 6");
   `iverilog-single-element-minus-select` is kept on its refused row at the lead's decision
   (nothing checks it while the row is refused, and the document says so).
4. **Texts** (`harness/sv/cases2.json`): the 11 `iverilog-*-init` declarations, `array_oob_inner`,
   `hier_fill_ctx` and `array_param_labels_l7` no longer say "No licensed-simulator
   confirmation is claimed"; each says what the pin shows. Only `observed` changed, and for
   `array_param_labels_l7` the `case_sha256` (the row gained `refusal`/`measured`); every other
   field (traces, ids, retirement conditions, digests) is byte-identical to HEAD. The DX2 text
   states that Xcelium's value trace equals Icarus's only through the partial-overhang rule and
   that its elaboration diagnostic (`BNDIPERR` prints the LRM label range) corroborates the
   declared label set.
5. **Corrections in the tree**: the headers of `array_oob.sv`, `array_oob_lsbwrite.sv`,
   `array_oob_part.sv` and `dyn32.sv`; the paragraph of `docs/sv-oracle-disagreements.md`
   that said overhangs "agree in every tool". The envelopes of those four DUTs were
   re-extracted (only the source digest and the span line numbers moved); re-extraction of
   the eleven fixtures this lane touches or adds is byte-identical to the committed
   envelopes.
6. **The pin** (`harness/sv/xcelium_golden.json`, Xcelium 24.03-s004, default flags, one run
   per row, through the refsim gate, one run at a time, in `/tmp/ta-r6/<label>/` on vip-ng via
   `LS_SV_XCELIUM_REMOTE_ROOT`; nothing was killed and nothing outside that directory was
   touched): the rows on the edited DUTs were re-run (traces identical, hashes moved); every
   new simulated row of lanes A and C was pinned, `param_types_ok*` in the restart; the 43
   rows that stopped simulating (41 by lane A, 2 by lane B) keep their entries as EVIDENCE
   (`test_xcelium_golden` now requires pinned rows to be rows of the corpus, not simulated
   ones, and that an evidence entry is a normal `ok` entry with the row's own cycle count).
   Lane B pinned its six admitted alias rows (`acg_alias_wr`, `acg_alias_copy`,
   `acg_alias_far`, `acg_alias_bits_ok`, `acg_alias_port_wr`, `acg_alias_hier_ok`) through a
   scratch copy merged back (six entries added, nothing else touched). The file now holds 465
   entries, all `ok`, 3693 cycle lines: 422 simulated rows (every simulated row of the 676 of
   `cases2.json` is pinned; the other 254 are loud-refusal rows) and 43 evidence entries.
7. **`docs/sv-xcelium-reference.md` section 6**: `-ii_val` ("Correct value for vector
   part-selects") repairs only reads whose base is a local variable and reads inside testbench
   tasks, functions and `initial`; it repairs no module-level read of a port or net base, no inner
   dimension and no write. The pin stays on the default flags; changing them re-keys every row
   (`XRUN_FLAGS` is part of `row_hash`). The table of diagnostics (`BNDWRN`, `BNDPERR`/`BNDIPERR`
   as hard errors for net-LHS and port-actual overhangs, `IIFAOB`/`IIRAOB`, `CUVMPW`, `BIGWBS`).
8. **`docs/sv-xcelium-audit.md` section 6**: P1, P2 and P3 are ONE Xcelium rule; the verified
   findings; the decisions table; the corrections; the open items (a 32-bit unsigned base, an
   extractor defect on element selects of packed-array members of packed structs, shift counts
   and array indices wider than 32 bits, the H1 guard's residue).

Verification (restart of 2026-10-29, afternoon). `python3 harness/sv/diff_test2.py --sim
iverilog --golden --no-xcheck` over the 46 rows this lane owns or touched (the P2 rows,
`dyn32`, the split fixtures, `array_oob_inner`, the eleven `iverilog-*-init` rows,
`hier_fill_ctx`, `acg_xproc_bits`, and the eight refused originals), through the Lean slot:
23 verified, 15 declared simulator disagreements, 8 loud refusals, 0 failures, exit 0; against
the pin 31 `XREF-MATCH`, 6 `XREF-DECLARED` (the six P2 rows), 1 `XREF-DIFF` (`dyn32`, the
open item: its 8 unsigned-base cells), 0 `XREF-STALE`, 0 `XREF-NONE`. The multi-point
cross-check was off for this run (it is orthogonal to the declarations). Offline suites:
`test_oracle_disagreements` 44, `test_xcelium_golden` 20, `test_xcelium_compare` 20,
`test_oracle_admission` 17, `test_xcelium_probe` 18, `test_ci_oracle_admission` 8, all OK;
`python3 tools/docs_check.py` OK.

Recorded gaps. (a) The whole-corpus `--golden` run (24.6 minutes in the audit) was not
repeated by this lane: the Lean slot is shared. What the lane relied on instead is that the
sources of every unchanged simulated row are byte-identical to the pinned ones (0
`XREF-STALE` among the 38 simulated rows it did run, and 0 among lane B's 26) and that the
pin holds an entry for every simulated row (checked by name against `cases2.json`). (b) No row of the
corpus is run LIVE on `xrun` by the harness; the P2 declarations are checked against the pin
(`--golden`), and the live path is covered by unit tests only. (c) The Xcelium diagnostics of
the reference document (`BNDIPERR` text, `-ii_val` effects) are verifier measurements, not
pinned data. (d) `iverilog-single-element-minus-select` sits on a refusal row and is not
checked. (e) The declared-divergence register (`docs/sv-declared-divergences.json`) holds
M0-mode provenance rows and was not touched. (f) `dyn32`'s unsigned-base cells and the
element select of a packed-array member of a packed struct stay open (audit 6.4).

## The clock-discipline guard (WP-Q0, refusal-only) — 2026-10-30

The first item (S0) of the sequential road (`svgolf/design/sequential/README.md`, approved by
Thomas on 2026-10-30). `Sem2.cycleStep2` runs every edge-phase process once per cycle and never
reads the clock's value, so the model is exact only when the clock is an input port of the top
whose edge is the cycle (the stimulus protocol: one entry, one rising edge) and silently wrong in
every other case. Measured on Xcelium 24.03-s004 and Icarus 12.0 (rows `clk_*`): an undriven or
constant-tied clock never captures (the model captured every cycle), a gated counter counts only
the enabled edges (`0 0 1 1 2 3 3` against the model's `0 1 2 3 4 5 6`), an internal-net clock
captures on the rising edges of its source only, a register used as a clock stays x, a design that
reads the clock as data gets the waveform where the model has no value.

**The rules** (`LeanModels/Sv/ClockGuard2.lean`, on the ELABORATED, flattened `Design2`): (1)
`Clock:source`, every edge process is clocked by a one-bit INPUT port of the top; (2) `Clock:reset`,
an asynchronous reset is an input port, not its own clock, and no signal is both a clock and a reset;
(3) `Clock:multiple`, at most one clock (several clocks are the note's S5/S6); (4) `Clock:data-read`,
nothing reads the clock as data, except the plain copy `assign t = clk` (what a bare instance
clock connection flattens to), whose target joins the clock's copy set and is checked in turn, and a
copy that reaches an output port is a data use; (5) `Instance:clock`, the existing Hier2 kind, now
also REPORTED at the loader, first, as the root cause. A refused design is the design itself with the
loud `Clock:*` process appended (`Design2.disciplineGuard`).

**Where.** A check BESIDE `name.sem`, exactly like `RangeGuard2.lean` and `CombAlias2.lean`: the
instantiation lemmas (`PDesign.instantiate2_eq`, `instantiateG2_of_ok`, `instantiateGD2_of_ok`,
`instantiateGD2_eq_driverGuard`, `Design2.driverGuard_of_ok`, `CombViewMain.lean`, the ∀-N
examples and every svGolf reference) are stated for the unguarded family, so a guard inside
`instantiateG2`/`instantiateGD2` would falsify them. The guard is run by `load_design_sv2` at the
defaults and at every probe-sidecar point (`Envelope2.clockAtPoints`), by `probeCheckString` (the svGolf
checker's entry), by `harness/sv/runner2.lean` at each row's point, and by `PDesign.clockReport`.
Edit set: `ClockGuard2.lean` (new), `Ingest2.lean`, `runner2.lean`, `diff_test2.py`
(`SV_LEAN_MODULES`), the register; `Hier2.lean` and every proof file are untouched.

**Trust.** The guard is a decidable function of the elaborated design and only refuses
(`disciplineGuard_of_admits`): it adds no axiom and no trusted statement. What an admitted design
satisfies is proved (`clockViolation_source`: every clock is a declared one-bit input port,
`clockViolation_single`: one clock, `clockViolation_reads`: nothing outside plain copies of the
clock's copy set reads it; `clockViolation_of_noEdge`: a combinational family is its own guard), all
on `propext`/`Quot.sound` only. The sequential statement's own `ClockedBy` is the proof-side twin.

**Corpus.** Of the 691 rows of `cases2.json` before this lane, 36 hold an edge process (34 on `clk`,
`Clk_CI` and `clk_i` two each) and ALL are admitted; no row violates. The M0 tier (`Design`, the
`clocked`, `counter`, `toggle`, `swap_nba`, `race_blk` examples) never passes through `Design2` and
is unaffected. 18 rows are new: 7 admitted designs (`clk_cnt`, `clk_cnt_n2`, `clk_shreg`,
`clk_pipe2`, `clk_fsm`, `clk_arst`, `clk_child_ok`) agree with Icarus and with the new pinned
Xcelium traces (additive, 7 entries); 11 refusal rows (`clk_undriven`, `clk_tied`, `clk_gated`,
`clk_internal`, `clk_reg`, `clk_data`, `clk_out`, `clk_two`, `clk_rst_int`, `clk_child_gated`,
`clk_child_data`) carry the Xcelium/Icarus measurement of what the unguarded model got wrong.
Fixtures: `Examples/system-verilog/sem2/clk_*` with the refusal messages pinned verbatim by
`#guard_msgs`.

## Genvar step spelled as an assignment (WP-L1) — 2026-10-30

`for (genvar i = 0; i < N; i = i + 1)` (IEEE 1800-2023 27.4 allows `g = g + 1` and `g += 1` besides
`g++`) was refused: the extractor kept the step as an `Unsupported` `AssignmentExpression` and
`stepDelta` only reads `.unary .inc/.dec`. The fix is in the extractor only (`_genstep`,
`_genstep_delta`, `_genstep_one`): the five spellings of the +/-1 step (`g = g + 1`, `g = 1 + g`,
`g += 1`, `g = g - 1`, `g -= 1`, parenthesised or not) are lowered to the SAME `Unary` `++`/`--`
node as `g++`/`g--`. Why not teach `stepDelta` a new node: the step is matched by `simp`/`rw`
lemmas (`stepDelta_inc`, `GenItem.expand2_genFor_ascending_*`, `CombView`'s `.unary .inc` pattern)
across the whole proof layer; a new constructor would have been a semantics change and a
tactic change, while one lowering keeps `LeanModels/Sv` byte-identical (nothing in the library
rebuilds) and is exactly slang's own reading of the loop. The condition for the lowering is
the type: the right operand must be the plain SIGNED 32-bit literal `1` in the genvar's
`integer` arithmetic. A parameter amount is never folded (it is a value at the default point
only), an unsigned or narrower literal (`1'b1`) changes the arithmetic type of `g - 1`, and a stride
(`g += 2`), `g * 2`, `1 - g` and `N - 1 - g` are not a +/-1 step; those are the loud
`GenerateFor:step`. Evidence: `extractors/sv/test_generate_steps.py`; `cases2.json` rows
`gstep_*`, `ripple_step*` (Icarus + pinned Xcelium, 0 differences) and the refusal rows
`gstep_stride`, `gstep_param`; `Examples/system-verilog/ripple_step` proves the adder for every `N`
with the unchanged tactics. Not done (not trivial): strides, and a step amount that is a parameter
expression (they need a general `stepDelta` and a tactic pattern for it).

## The binary XNOR `~^` / `^~` in the symbolic tier (WP-L2) — 2026-10-30

`a ~^ b` and `a ^~ b` (IEEE 1800-2023 11.4.8, Table 11-14) are one slang operator (`BinaryXnor`),
which the symbolic extractor refused. It is now lowered, in SIGNAL expressions, to `~(a ^ b)`:
`Unary "~"` over `Binary "^"`, the nodes `instExpr2`, `Expr2` and every proof already know. Why a
lowering and not a native `BinOp.xnor`: the constructor would sit in `Ast.lean`, under the whole
`LeanModels.Sv` chain, and every exhaustive match on `BinOp`, the evaluator, the lowering lemmas and
the tactics would change and rebuild, for a table that is the composition of two pinned ones.
Why it is exact: slang has converted both operands to the expression's own type, so the inner `^` and
the outer `~` are typed as the xnor was (same context width, same signedness); `x ^ y = x` for any x/z
operand bit and `~x = x`, so the result bit is x exactly where Table 11-14 says; equal known bits give
1, which includes the extension bits of a wider context (`0 ~^ 0 = 1`, measured: 8-bit operands into a
16-bit target give an all-ones upper byte on Xcelium 24.03, Icarus 12.0 and the model). Symbolic-constant
positions (parameter defaults, localparams, generate conditions) are NOT lowered: the constant tier
(`Param.lean` `evalInt`) refuses an INT-class `~` and has its own sized rule, none measured against the
lowering, so they stay `BinaryExpression:BinaryXnor`, refused at the defaults by `load_design_sv2`
(message pinned in `Examples/system-verilog/sem2/xnor_const`) or loud in `name.sem`
(`xnor_genconst`). A signed operand pair assigned to a wider target needs sign extension, which the
tier does not have: `ConversionExpression:width`, exactly as for `$signed(a) ^ $signed(b)` (measured: the
simulators sign-extend, `xnor_sgn_wide`). The reduction `~^a` was already admitted and is pinned by
rows. The proof: `Examples/system-verilog/xnor_n/proof.lean` shows for every width and every 4-state
vector pair that the lowered expression is the bitwise `xnorTable` written out from the standard, and
that `xnor_n.sem N` is that one process. The sv_comb recognizer is unchanged: it rejects every unary
operator, which is the `~` item of the always_comb work; once `~` is in the fragment, `~(a ^ b)` is
covered by it. Regression evidence: every committed symbolic envelope re-extracts byte-identical
(the lowering only fires where the extractor emitted an Unsupported before).

## Dynamic whole-net continuous-driver resolution — 2026-10-31

The timed scheduler now retains one sampled value per live whole-net `assign` process and resolves the target after each driver publication. Ordinary strength-free four-state resolution follows the IEEE net rule for this admitted shape: all `z` drivers produce `z`, equal known drivers preserve that value, and an `x` or disagreement produces `x`. The resolved signal is therefore no longer the last process to run; later Active ordering cannot erase an earlier driver's contribution. The driver table is initialized with the process table and threaded through blocking, delayed, and re-armed process completions. Literal/static overlaps keep their existing folding rules, while selected or concatenated dynamic targets and variable multiple-driver forms remain loud; the existing `assign_multiple_drivers` refusal is unchanged.

`assign_net_resolution` drives an internal `wire y` from live `a = 0` and `b = 1` sources and observes `1'bx` after a delay. The extractor preserves both dynamic whole-net `Assign` processes, the loader checks declared net targets, and the timed runner resolves the two samples. Differential coverage moves **539/525/0/14 → 540/526/0/14** (rows/agree/disagree/recorded refusals); grammar coverage remains **239/210/29**, and the sv-tests-2 extraction census remains **5,901 clean of 22,071 paths**.

## `always_ff` edge capture witness — 2026-10-31

The timed `always_ff` acceptance row now exercises the retained positive-edge process instead of only proving that the process can be loaded. `always_ff_capture` changes `d`, raises `clk` twice, and checks that each edge queues the nonblocking update; the final value proves that the scheduler's existing edge registration and NBA commit are used for the distinct `always_ff` process kind. No new event loop or edge-specific shortcut is added.

Differential coverage grows **540/526/0/14 → 541/527/0/14**; grammar coverage remains **239/210/29**, and the sv-tests-2 extraction headline remains **5,901 clean of 22,071 paths**.

## `always_latch` wake and hold witness — 2026-10-31

The timed `always_latch` row now changes its enable and data after time zero. `always_latch_wake` verifies that the inferred level-sensitive process captures when enabled and retains its previous value when disabled, using the existing signal-change wake queue. No polling process or latch-specific scheduler path is added.

Differential coverage grows **541/527/0/14 → 542/528/0/14**; grammar coverage remains **239/210/29**, and the sv-tests-2 extraction headline remains **5,901 clean of 22,071 paths**.
