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
path and currently admits retained `initial` bodies in source order. Extractor, ingestion,
evaluator and kernel-loader refusal inventories must therefore stay separate.

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
dynamic, arithmetic, negative, unknown, real/time-literal, intra-assignment,
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
reinstates the wait after each completed body. `AlwaysComb`, continuous assigns,
and all other process kinds remain loud in the timed loader.

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
value/storage types and integral membership expressions retain their
existing missing mechanisms. See [the operator contract](sv-wildcard-equality.md).

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

The ordinary portable suite includes x/z stimuli and an absent-input cycle:
all five complete cycle traces agree with both independent simulation and
Icarus. The separate unconnected startup fixture differs: Icarus 13.0
development build `dad78d525` retains z in unconnected two-state input ports,
while independent simulation initializes them to zero. This is recorded as
a simulator divergence, not a model pass. The new integral-variable-port
slice supersedes the older input-port refusal below.

### Constant `$clog2` calls — 2026-10-14

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

Enum methods, dynamic `$cast`, packages/imports, enum ports/nets, unpacked
containers and unsupported base ranges remain loud. The symbolic
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
`&&`, reusing the existing four-state scalar operators. Unequal shapes and
unsupported aggregate types remain loud. The `unpacked_compare` fixture checks
whole-array and slice comparisons through Lean and the self-check runner.

The external `sv-tests-2` checkout was unavailable for this turn, so the
committed census snapshot is unchanged and this rung makes no fresh
whole-corpus coverage claim. Focused comparison tests establish the admission
boundary; the next census rerun will price any newly clean rows.

### Fixed-array case equality and inequality — 2026-10-19

Equal-length whole fixed-unpacked arrays and simple constant slices now lower
`===` and `!==` to pairwise cell case comparisons joined by logical `&&`, so
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
is sampled once; excess source MSBs are consumed by the existing packed resize.
Left streaming, nested/effectful streams, packed-struct or unpacked aggregate
leaves, and narrower sources remain loud. The `streaming_unpack` fixture checks
the real envelope through Lean and the self-check runner, without a new
simulator-agreement claim. The fresh **22,033**-path census reports **2,960
clean / 19,007 partial / 66 include skips** with zero extraction errors: seven
clean gains and no losses; `AssignmentExpression:target` falls **3,928 →
3,920**.

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

Two-state selected sources stay loud: available oracle behavior disagrees
on out-of-range reads, so this item does not claim their semantics.
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
structs/unions, nested unions, unpacked or dynamic members remain loud; these
semantic fixtures do not claim a legacy census gain or simulator agreement.

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
nested unions and other aggregate paths remain loud. This is a symbolic
fixture result only, with no legacy census or simulator-agreement claim.

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
