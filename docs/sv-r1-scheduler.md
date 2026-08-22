# R1 — THE SCHEDULER: census and design

**Status: the design for rung R1 of `docs/sv-charter.md` §8.3.** Ruling
§6.4 put the full IEEE 1800 clause-4 scheduler in scope and sequenced it
early; §8.1 settled it as the rung immediately after consolidation. This
document is the census that must precede the modelling, and the design
it licenses. **No Lean lands with it.**

No IEEE text is reproduced anywhere. Clause numbers and paraphrase only,
per the family law; the standard's own PDF stays unopened.

---

## 0 THE HEADLINE, and a correction to the number that ordered this rung

The charter published *"50 of 98 proof-carrying declarations (51%) are
trace-shaped"* as the metric that put the scheduler before breadth.
**Re-measured across the whole estate, that number was scoped wrong
twice** — it counted only `LeanModels/Sv/` and its regex missed the
`⊨`/`⊑` surface forms, so it silently excluded every theorem about an
actual design.

| estate | proof-carrying | trace-shaped | of those, plumbing |
| --- | ---: | ---: | ---: |
| `LeanModels/Sv/` | 98 | 61 | 23 |
| `Examples/system-verilog/` | 133 | 95 | 0 |
| **TOTAL** | **231** | **156 (68%)** | **23** |

*(Counting rule: `docs/sv-charter.md` §7.4, applied to both trees.
"Trace-shaped" = the statement or proof mentions `run`/`Runs`/`runFrom`/
`cycleStep`/`combSettle`/`edgePass`/`SvState`/`⊨`/`⊑`.)*

**156 of 231, not 50 of 98.** The correction does not weaken §8.1's
ordering — **it strengthens it three-fold.** Two thirds of the estate is
trace-shaped, the `Examples/` half is entirely *semantic* content rather
than plumbing, and all of it grows with every construct rung. This is
the fourth self-correction this lane has published, and like the other
three it was invisible until something was actually run.

**But the same census produces the design that makes the number nearly
moot** (§5): because the cycle model *refuses* rather than answers
outside its fragment, R1 can be a conservative **extension**, and the
156 transfer through one adequacy lemma instead of being restated.

---

## 1 THE REGION CENSUS — clause 4, paraphrased

### 1.1 What clause 4 is

IEEE 1800-2023 clause 4 specifies simulation as an **event-driven**
process over a totally ordered sequence of **simulation times**
(§4.2-4.3). At each simulation time the pending events are partitioned
into an ordered family of **regions** — the *stratified event scheduler*
(§4.4) — and the standard fixes both the region order and, within
several regions, exactly what may and may not be assumed about
execution order (§4.6-4.7).

Two things make this cheaper to model than C's memory model, which the
charter already noted: it is written as an **operational algorithm**
(§4.5 gives a reference algorithm directly), and its nondeterminism is
**enumerable** — a choice among ready processes, not a tangle with
aliasing.

### 1.2 The fifteen regions

Nine core simulation regions, and six PLI regions interleaved among them
(§4.4). In order within one time slot:

| # | region | kind | what enters it (§4.4 subclauses) |
| ---: | --- | --- | --- |
| 1 | **Preponed** | core | sampling for concurrent assertions and clocking-block inputs — values read *before* anything in the slot changes them |
| 2 | Pre-Active | PLI | PLI callback point |
| 3 | **Active** | core | blocking assignments; continuous-assignment evaluation; primitive evaluation; `$display`; **RHS evaluation** of nonblocking assignments |
| 4 | **Inactive** | core | processes resumed from `#0` |
| 5 | Pre-NBA | PLI | PLI callback point |
| 6 | **NBA** | core | the **LHS updates** of nonblocking assignments scheduled earlier in this slot |
| 7 | Post-NBA | PLI | PLI callback point |
| 8 | **Observed** | core | concurrent-assertion property expressions evaluated; pass/fail code scheduled |
| 9 | Post-Observed | PLI | PLI callback point |
| 10 | **Reactive** | core | program-block code (cl. 24); assertion action blocks; clocking-block output drives |
| 11 | **Re-Inactive** | core | `#0` within the reactive set |
| 12 | Pre-Re-NBA | PLI | PLI callback point |
| 13 | **Re-NBA** | core | nonblocking updates scheduled from the reactive set |
| 14 | Post-Re-NBA | PLI | PLI callback point |
| 15 | **Postponed** | core | `$strobe`, `$monitor` — read-only; **no value may change here** |

**The iteration structure is the part a naive model gets wrong.** The
regions are not a single pass. Active/Inactive/NBA form a loop: work
scheduled into Active by an NBA update re-enters Active, and the slot
does not advance until that set is exhausted. Observed/Reactive/
Re-Inactive/Re-NBA form a second loop that can schedule *back* into
Active. Only when nothing remains does Postponed run and the slot close.

**Three consequences that are load-bearing for the tier.**

1. **`<=` is split across two regions.** RHS in Active, LHS update in
   NBA. This is exactly why nonblocking assignment gives
   sample-then-commit, and the current cycle model already implements
   precisely this split — see §5.
2. **Preponed is what makes clocking blocks and assertions well-defined**
   (cl. 14, cl. 16). Sampling *before* the slot's activity is what
   removes the race between a clock edge and the data it clocks.
3. **Postponed is read-only.** A model that lets a Postponed action
   write is not conservative — it is wrong.

### 1.3 The PLI regions, and the scope ruling

Ruling §6.3 puts everything in scope, so the six PLI regions are
in-scope *eventually*. They are, however, **callback points rather than
semantics**: nothing in them is specified as executing SystemVerilog.
The design below carries them as constructors from day one — so the
region type never has to change again — while leaving their inhabitants
empty. **Naming them costs one constructor each; retrofitting them
later would change the region type and re-open everything a second
time.** That asymmetry is the whole argument for including them now.

---

## 2 THE DETERMINISM BOUNDARY

**This is the most important section in the document.** The boundary is
not a detail of the scheduler — under the tier's doctrine, `∀ σ` ranges
over exactly the freedom the standard grants, so **the boundary IS the
definition of `⊨`.** Draw it too wide and true theorems become
unprovable; draw it too narrow and the tier proves things about
SystemVerilog that are not true.

### 2.1 What the standard FIXES — must NOT be ∀-quantified

Per §4.6 (determinism) and the assignment clauses:

* **Region order.** Preponed before Active before Inactive before NBA
  before Observed before Reactive before Re-Inactive before Re-NBA
  before Postponed. Fixed, always.
* **Statement order within a `begin`...`end`.** Statements in a
  sequential block execute in the order written (§4.6). A process is not
  free to reorder its own statements.
* **NBA update order to the same variable.** Nonblocking updates to one
  variable, scheduled within one time slot, are applied in the order
  they were scheduled (§4.6, cl. 10.4.2) — last one scheduled wins, and
  *which* is last is determined, not chosen.
* **Preponed sampling.** What Preponed observes is the pre-slot value.
  Not a choice.

### 2.2 What the standard LEAVES FREE — exactly the ∀

Per §4.7 (nondeterminism) and §4.8 (race conditions):

* **The selection order of ready processes within a region.** When
  several processes are ready in Active, the simulator picks one, may
  run it to completion or to a suspension point, and then picks again.
  **This is the freedom the oracle models, and it is the whole source of
  the races the tier already proves things about.**
* **Interleaving at suspension points.** A process that suspends
  (`@`, `wait`, `#`) yields, and what runs next is free.
* **`#0` ordering.** Multiple processes resumed in Inactive have no
  guaranteed relative order.
* **Evaluation order among independent continuous assignments and
  primitives.**

### 2.3 The boundary, stated as the oracle's contract

> **The oracle chooses, at each invocation, a permutation of the ready
> process list WITHIN ONE REGION. It never chooses the region order, the
> statement order inside a process, or the NBA application order.**

The current `ScheduleOracle` already has exactly this shape:

```lean
structure ScheduleOracle where
  choose : Nat → List Nat → List Nat
  choose_perm : ∀ (k : Nat) (ready : List Nat), (choose k ready).Perm ready
```

`choose_perm` is the legality proof, which is what makes `∀ σ` range
over *legal* schedules rather than arbitrary functions. **The M0 design
got the shape right;** R1 adds one parameter (§4.2). That is a stronger
starting position than this rung had any right to expect, and it is why
the region upgrade is an extension rather than a rewrite.

---

## 3 THE CORPUS PRICE — which regions actually matter

Which regions to build first is a measurement, not a preference. Counted
with `rg -l` over both corpora (file counts; a construct is counted once
per file). `sv-tests-2` figures are over its 21 186 `chapter-*` files.

| construct | drives region | sv-tests-2 files | % |
| --- | --- | ---: | ---: |
| **`initial`** | **Active (+ time)** | **20 939** | **98.8%** |
| `#<n>` delay | time advance / Inactive | 9 903 | 46.7% |
| `assert property` | **Observed** | 1 777 | 8.4% |
| `event` | Active (suspension) | 1 181 | 5.6% |
| `clocking` | **Preponed** | 827 | 3.9% |
| `##` cycle delay | Preponed | 698 | 3.3% |
| `fork` | Active (interleaving) | 642 | 3.0% |
| `program` | **Reactive** | 548 | 2.6% |
| `#0` | **Inactive** | 356 | 1.7% |
| `final` | Postponed-adjacent | 235 | 1.1% |
| `always_ff` | Active/NBA | 229 | 1.1% |
| `always_comb` | Active | 222 | 1.0% |
| `join_none` | Active | 264 | 1.2% |
| `wait(` | Active (suspension) | 96 | 0.5% |
| `always_latch` | Active | 56 | 0.3% |
| `$monitor` | **Postponed** | 47 | 0.2% |
| `$strobe` | **Postponed** | 40 | 0.2% |

### 3.1 THE HEADLINE: the anchor corpus is 99.2% out of reach

Files containing **none** of `initial`, `#<n>`, `fork`, `clocking`,
`assert property`, `program`, `wait(`, `##`, `final` — i.e. files the
present cycle model could in principle execute:

| corpus | total | cycle-fragment-only | share |
| --- | ---: | ---: | ---: |
| **sv-tests-2** (anchor) | 21 186 | **171** | **0.80%** |
| public `sv-tests` | 1 034 | 451 | 43.6% |

**Four fifths of one percent.** The tier's current scheduler can reach
almost nothing in the corpus every coverage claim is measured against.

**Why the two corpora differ so sharply** is itself the finding, and it
is not a discrepancy: `sv-tests-2` is a *simulation* corpus — its tests
are self-checking, so nearly every file drives stimulus from an
`initial` block and prints a verdict. The public suite carries a large
population of parse- and elaborate-only tests that never run, which is
why 43.6% of it contains no scheduling construct at all. **A corpus of
runnable tests is an `initial`-shaped corpus.** Any conformance ladder
scored on simulation is therefore gated on `initial` before anything
else.

### 3.2 What this re-orders

The charter framed the expensive half of clause 4 as the *reactive*
family (Observed/Reactive/Re-NBA — clocking blocks, program blocks,
assertions). The corpus disagrees about priority, though not about cost:

* **`initial` alone unlocks 98.8%** and needs only the **Active** region
  plus the ability to advance time. It is one process kind and a time
  loop, not a new region family.
* **`#<n>` delays reach 46.7%** and need time advancement — the same
  machinery.
* The reactive family is a **long tail by file count**: assertions 8.4%,
  clocking 3.9%, programs 2.6%. Expensive *and* rarer.
* **Postponed is nearly unused** — `$strobe` 0.2%, `$monitor` 0.2% —
  which is why §4.4 can implement it as a write-prohibited no-op and be
  right about essentially the whole corpus.

**So inch 4's internal order is decided by measurement**: Active with a
time loop first (`initial`, `#`), Inactive next (`#0`, 1.7%), and the
reactive family last — which is exactly what §7 inch 9 already defers,
now with a number behind it rather than an intuition.

One caution on the method: these are **lexical** counts. `\binitial\b`
does not distinguish an `initial` block from the word in a comment, and
the metadata headers were not stripped for this table. The counts are
therefore upper bounds — but at 98.8% the conclusion is not sensitive to
the error bar, and the independent M0 census agrees in direction: only
**806 of 21 186 files (3.8%)** extract with zero `Unsupported` nodes.

---

## 4 THE LEAN SHAPE — proposed

### 4.1 The region type, complete from day one

```lean
/-- The stratified event regions of IEEE 1800-2023 §4.4, in slot order.
PLI regions are carried as constructors with no inhabitants at R1 so the
type never has to change again (§1.3). -/
inductive Region where
  | preponed
  | preActive                              -- PLI
  | active | inactive
  | preNBA                                 -- PLI
  | nba
  | postNBA                                -- PLI
  | observed
  | postObserved                           -- PLI
  | reactive | reInactive
  | preReNBA                               -- PLI
  | reNBA
  | postReNBA                              -- PLI
  | postponed
deriving Repr, BEq, DecidableEq, Inhabited
```

### 4.2 The oracle — one new parameter

```lean
structure ScheduleOracle where
  choose : Nat → Region → List Nat → List Nat
  choose_perm : ∀ k r ready, (choose k r ready).Perm ready
```

The old oracle embeds as `fun k _ ready => …`, so `σ_src`, `σ_rev` and
`revWhen` extend by ignoring the region argument, and **every existing
`∀ σ` theorem keeps its meaning**. Region-sensitive witnesses (a
schedule that reorders only in Active) become expressible, which is
what the race theorems will want.

### 4.3 The slot, and the trace

The design question R1 turns on is *what a trace is*. The proposal keeps
the trace a list — one entry per **time slot** rather than per cycle —
and records the two states any observer can see:

```lean
/-- One simulation time slot. `sampled` is what Preponed observed (what
clocking blocks and concurrent assertions see); `final` is the state
after the slot closes, which is what Postponed reads and what any
cycle-level observer sees. -/
structure Slot where
  time    : Nat
  sampled : SvState
  final   : SvState
deriving Repr, Inhabited

abbrev RegionTrace := List Slot
```

**Why not a full per-region state sequence?** Because nothing outside
the slot can observe intermediate region states — Postponed is read-only
and runs last, so `final` is exactly the slot's observable. Carrying the
intermediate states would make the trace type richer than the
observation relation, and every theorem would then quantify over
detail no property can mention. **The trace should be as coarse as the
observations and no coarser**; `sampled` earns its place only because
clocking blocks and assertions genuinely observe it.

### 4.4 The step function

```lean
def slotStep (d : Design) (σ : ScheduleOracle) (fuel : Nat)
    (inputs : SvState) (st : SvState) (k : Nat := 0) : Res (Slot × SvState × Nat)
```

with the internal shape following §1.2's iteration structure: a
Preponed sample; then the Active/Inactive/NBA loop to exhaustion; then
Observed; then the Reactive/Re-Inactive/Re-NBA loop, which may schedule
back into Active; then Postponed under a **write-prohibition** that
refuses loudly rather than silently dropping a write.

Fuel bounds both loops. The existing `Res` covenant carries the
outcomes unchanged: `.timeout` means a loop did not converge (which is
now a *real* SystemVerilog condition, not only a comb loop), and
`.unsupported` stays loud and fuel-independent.

---

## 5 EXTENSION, NOT SUPERSESSION — and why that is provable here

### 5.1 The fact that makes it work

The charter required the mapping be an **extension** where the cycle
model is faithful and a **supersession-with-adequacy** where it is not,
and *never a silent replacement*. Measured, the answer is better than
that dichotomy:

`LeanModels/Sv/Ast.lean`'s `Process` has exactly five constructors —
`alwaysFF`, `alwaysPlain`, `alwaysComb`, `assign`, and
**`unsupported (svKind) (text)`**. Everything clause 4 would newly reach
— `initial`, `#`, `fork`/`join`, `wait`, clocking blocks, program
blocks, assertions — extracts to `Process.unsupported` today, and
`Semantics.lean` refuses on it (17 `unsupported` sites).

> **So outside its fragment the cycle model does not give a wrong answer;
> it gives NO answer.** There is nothing to supersede, because there is
> nothing to contradict. R1 is a conservative extension, and adequacy is
> needed only *on* the fragment.

This is the dividend of the "never hide errors" law, collected a month
after it was paid: **because the dormant tier refused loudly instead of
guessing, its successor can extend it instead of replacing it.**

### 5.2 The fragment predicate

```lean
/-- The cycle-level fragment: every process is one of the four the M0
tier supports. Decidable, and checked by `decide` on any concrete
design. -/
def Design.isCycleFragment (d : Design) : Bool :=
  d.processes.all fun p => !p.isUnsupported
```

### 5.3 `cycleOf` and the adequacy lemma

```lean
/-- The cycle-level view of a region trace: the state each slot closes in. -/
def cycleOf (tr : RegionTrace) : List SvState := tr.map (·.final)

/-- ADEQUACY. On the cycle fragment, the region semantics projects exactly
onto the cycle semantics — same schedule, same fuel, same stimulus. -/
theorem cycleOf_runRegion (d : Design) (h : d.isCycleFragment = true)
    (σ : ScheduleOracle) (fuel : Nat) (stim : List SvState) :
    (runRegion d σ fuel stim).map cycleOf = run d σ fuel stim
```

**This one lemma is what the 156 trace-shaped declarations cost.**
With it, a theorem stated about `run` transfers to `runRegion` by
rewriting, rather than being re-proved. Without it, each is re-opened
individually.

**It is not free, and the charter should not pretend otherwise.** The
proof is an induction over `stim` whose step obligation is that one
`slotStep` on a fragment design agrees with one `cycleStep`. That step
is where the real content sits: it must show that on a fragment design
the Preponed sample is unobserved, Inactive and the reactive family are
empty, Postponed is a no-op, and the Active/NBA loop settles in exactly
the pattern `cycleStep` hard-codes — comb settle, edge pass with
blocking-immediate and NBA-queued, commit, comb settle. **That is a
genuine theorem, and it is the honest price of the rung.** It is also
the *right* place for the difficulty: it is proved once, against the
plumbing, rather than 156 times against designs.

### 5.4 What still moves

Adequacy makes the 156 transfer, but three things need real work:

1. **The 23 plumbing lemmas** (`_le`/`_mono`/`fuelMono`) are statements
   about the *interpreter*, not about traces, so they must be re-proved
   for `slotStep` and `runRegion`. They follow the definition tree
   mechanically — the existing ladder (`evalExpr_le` → … → `run_le`)
   is the template and gains one rung per new loop.
2. **`Sv.Deterministic` becomes sharper and must be re-examined.** It
   currently says all schedules give the same trace. Under regions, the
   same statement is *stronger* (more schedules exist), which is
   correct — but the `race_blk` witnesses must be re-checked to confirm
   they still separate, now as region-tagged schedules.
3. **The surface notations** (`⊨`, `⇓[σ]`, `⊑@clk`) elaborate to the
   cycle judgment. `⊑@clk` in particular is *defined* in cycles, and
   under regions "cycle" is derived — so it should be re-defined
   through `cycleOf`, which is exactly the discipline §6 applies to the
   divider.

---

## 6 THE DIVIDER, STATED cycleOf-FROM-LINE-ONE

Ruling §6.6 makes the divider a milestone on this rung, and §8.2 chose
Order B (scheduler first) with one exception: the already-ingested
integer divider may be stated earlier **provided it is stated through
`cycleOf` from the first line**. Concretely, that means never writing
`run` in a divider statement.

**The shape to write today**, which survives R1 untouched:

```lean
/-- The observable of a serial divider: the quotient signal at the slot in
which `done` is first asserted. Stated over the CYCLE VIEW of a trace, so
it reads identically before and after the region upgrade. -/
def divResult (tr : List SvState) (doneSig quotSig : String) : Option LVec := …

/-- Rung A: the integer divider computes signed 32-bit quotient/remainder.
Note what this does NOT mention: `run`, `cycleStep`, or `Slot`. It
quantifies over schedules, and observes through `cycleOf`. -/
theorem alu_div_correct (σ : ScheduleOracle) (fuel : Nat) (stim : List SvState)
    (tr : RegionTrace)
    (h : RunsRegion cv32e40p_alu_div σ fuel stim tr) … :
    divResult (cycleOf tr) "result_o" "ready_o" = some (expectedQuotient a b)
```

**Before R1 lands**, the same theorem is stated against the cycle
semantics with `cycleOf` as the identity on `List SvState` — a
definitional stub — so the *statement text does not change* when the
region model arrives; only the stub's definition is replaced and the
adequacy lemma discharges the difference. **That is the entire trick,
and it costs one definition today.**

The IEEE 754 rung (HardFloat `divSqrtRecFN`) inherits the same shape.
Its own obstacles are unchanged and are not scheduler problems: the
`recFN` recoding must be composed through, it is Verilog rather than
SystemVerilog, and it is gated on the shared SoftFloat spec layer.

---

## 7 PRICED INCHES

R1 is **census → boundary → shape → adequacy → semantics → re-establish**,
in that order. The census (§1-3) and the boundary (§2) land with this
document.

| inch | deliverable | price |
| ---: | --- | --- |
| 1 | **This document** — region census, determinism boundary, corpus price | LANDED |
| 2 | `Region`, the widened `ScheduleOracle`, `Slot`/`RegionTrace`, `isCycleFragment`, `cycleOf` — **types only**, no semantics | small; ~80 lines, no proofs |
| 3 | The `cycleOf` stub + the divider statement shape (§6), against today's cycle semantics | small; unblocks rung A immediately |
| 4 | `slotStep`: Preponed sample, Active/Inactive/NBA loop, Postponed write-prohibition. **Reactive family stubbed as empty, refusing loudly if reached** | the bulk of the rung |
| 5 | **The adequacy lemma** `cycleOf_runRegion` on the fragment | the hard theorem; the rung's centre |
| 6 | Re-prove the 23 plumbing lemmas against `slotStep`/`runRegion` | mechanical, follows the definition tree |
| 7 | Transfer the 156: rewrite `run` → `cycleOf ∘ runRegion`, re-check `Deterministic` and the `race_blk` witnesses, re-define `⊑@clk` through `cycleOf` | mostly mechanical *given* inch 5 |
| 8 | Extractor + envelope: stop emitting `Process.unsupported` for `initial` and `#`; `language_version` first-class (charter §7.2 retrofit 3) | one function each; **21 envelope regens, gated by `sv_round_trip.py`** |
| 9 | The Reactive family for real — program blocks, clocking blocks, assertions | a rung of its own; explicitly deferred past R1 |

**Inches 2 and 3 are trivially landable now** and are worth landing
before inch 4, precisely because they let rung A's divider statement be
written in its final form while the semantics is still being built.

---

## 8 WHAT THIS DESIGN DOES NOT DECIDE

* **The event-queue representation** inside `slotStep`. The regions are
  fixed by §1.2; how the pending set is carried is an implementation
  choice deferred to inch 4.
* **Whether `Slot.time` is `Nat` or a richer time type.** `#` delays
  need arithmetic on it; `timeunit`/`timeprecision` (cl. 3) may force a
  scaled representation. Deferred until inch 4 measures what the corpus
  needs.
* **The Reactive family's semantics** — deferred to inch 9 by design,
  and refusing loudly until then.
* **Assertion semantics** (cl. 16, Annex F). Observed is *named* here
  and left empty; Annex F gives concurrent assertions a formal semantics
  in the standard itself, which is a gift to be collected on its own
  rung.
* **Whether `Sv.Res` moves to `Core/`.** Unchanged from the charter:
  structural, and triggered by the C tier's M2, not by SV.
