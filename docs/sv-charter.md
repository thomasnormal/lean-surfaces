# The SystemVerilog tier: FOUNDING CHARTER

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
delay remains loud because Inactive delivery is not in the public kernel path;
dynamic, arithmetic, negative, unknown, real/time-literal,
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
ranges, aggregates, and symbolic signed/two-state declarations remain loud.
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
declarations and uses. It occurs in 5,743 files, but is the sole refusal in 28;
the common companions are other storage, call, class, and selected-access
boundaries. The symbolic `PDecl`/`PType` surface has no two-state metadata and
keeps `Squash2` loud, so a blanket declaration flag would fabricate semantics
for representations the tier does not have. The complete admitted slice and
the measured refusal rationale are recorded in
[`sv-two-state-boundary.md`](sv-two-state-boundary.md). No aggregate, object,
string/real, handle, or event scheduler is smuggled into this rung.

The ordinary portable suite includes x/z stimuli and an absent-input cycle:
all five complete cycle traces agree with both independent simulation and
Icarus. The separate unconnected startup fixture differs: Icarus 13.0
development build `dad78d525` retains z in unconnected two-state input ports,
while independent simulation initializes them to zero. This is recorded as
a simulator divergence, not a model pass. The new integral-variable-port
slice supersedes the older input-port refusal below.

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
it is enough for the six M0 designs and the CV32E40P modules. It does
**not** model the full region semantics: the timed loader has only the narrow
positive-literal `initial`/`#d` bridge documented above; the Inactive region,
Observed / Reactive (so no clocking blocks, no program blocks), or Postponed.
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
timed clocks, zero-delay Inactive delivery and symbolic-mode loops remain loud.

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
syntax, unsupported types/storage, dollar case endpoints and array-element
widening remain loud. The symbolic structural case path is unchanged.
See [the contract](sv-case-inside.md).

The paired **22,035**-path census gains **21 clean files** without losses:
**3,350 → 3,371 clean**, **18,619 → 18,598 partial**, **66 include skips**,
zero extraction errors. All twenty-one gains match complete independent
transcripts under both source and reverse schedule oracles. Three authored
sources also match complete transcripts, including all 256 pairs of two-bit
four-state operands, type/range/array contexts and delayed live-value changes.
A fourth source explicitly preserves the case-array widening discrepancy as
a refusal; it is not a runtime match. Three fixture-bound kernel theorems prove
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
