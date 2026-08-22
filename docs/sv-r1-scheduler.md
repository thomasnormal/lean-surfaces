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

Which regions to build first is a measurement, not a preference.

**Method, and a correction to this section's first draft.** The counts
below strip `//` and `/* */` comments with a character scanner, blank
out string-literal bodies (so `$display("always @…")` cannot match), and
drop surviving `:key:` metadata lines. **This section first published
raw `rg -l` counts, flagged as upper bounds; several were materially
off** — `final` by 1.8x, `event` by 3.3x, `$monitor` by 2.9x, `clocking`
by 1.17x. The 98.8% headline survived unchanged, but the caveat was
doing real work and the filtered numbers replace the raw ones here.
Corpus A is all **21 631** `.sv` files; B is **1 034**.

One corpus fact governs everything below: **A is 85.2% runtime tests**
(18 426 files tagged `:type: simulation`), where **B is 33.4%** and 418
of its files (40.4%) contain no process of any kind. A is a simulation
suite; B is largely a parser suite.

### 3.1 Ranked, corpus A (21 631 files)

| construct | files | % | region |
| --- | ---: | ---: | --- |
| **`initial`** | 21 382 | **98.8** | Active + time |
| **`$finish`** | 20 973 | **97.0** | Active |
| **`$display`** | 20 056 | **92.7** | Active |
| **`#` delay** (nonzero) | 10 033 | **46.4** | time wheel |
| standalone `@(…)` | 3 063 | 14.2 | Active (suspend) |
| blocking `=` in `always` | 3 173 | 14.7 ±1pp | Active |
| `always #d` clock-gen | 2 731 | 12.6 | time wheel |
| `assign` | 2 080 | 9.6 | Active |
| `class` | 2 040 | 9.4 | *(not a region)* |
| `assert property` | 1 796 | 8.3 | Observed |
| **nonblocking `<=`** | **1 091** | **5.0** | **NBA** |
| `covergroup` | 808 | 3.7 | Preponed |
| `clocking` | 705 | 3.3 | Preponed |
| `##` cycle delay | 690 | 3.2 | Preponed |
| `fork` | 629 | 2.9 | Active (interleave) |
| `program` | 467 | 2.2 | Reactive |
| `event` decl / `->` trigger | 360 / 260 | 1.7 / 1.2 | Active |
| `#0` | 283 | 1.3 | Inactive |
| `always_ff` / `always_comb` / `always_latch` | 206 / 177 / 32 | 1.0 / 0.8 / 0.1 | Active + NBA |
| `final` | 130 | 0.6 | Postponed-adjacent |
| `wait(` | 94 | 0.4 | Active (suspend) |
| `$strobe` / `$monitor` | 29 / 16 | 0.1 / 0.1 | **Postponed** |

### 3.2 Rollup by region — union of files needing it

| region | corpus A | corpus B |
| --- | ---: | ---: |
| **Active** | **21 438 (99.1%)** | 618 (59.8%) |
| *(time wheel — not a region)* | **10 443 (48.3%)** | 134 (13.0%) |
| Preponed | 3 285 (15.2%) | 46 (4.4%) |
| Reactive | 2 870 (13.3%) | 46 (4.4%) |
| Observed | 2 038 (9.4%) | 57 (5.5%) |
| **NBA** | **1 091 (5.0%)** | 53 (5.1%) |
| Inactive | 283 (1.3%) | 4 (0.4%) |
| Re-NBA | 258 (1.2%) | 2 (0.2%) |
| Re-Inactive | 38 (0.2%) | 0 |
| Postponed | 43 (0.2%) | 2 (0.2%) |

**The surprise, and it corrects an assumption this tier was built on:
NBA is a LONG-TAIL region, not a core one.** Only **5.0%** of corpus A
and 5.1% of B contain any nonblocking assignment. Only **15.6%** of A
contains an RTL process (`always*`/`assign`) of any kind. **These are
language-semantics suites, not RTL corpora** — and the M0 tier was
designed around `always_ff`/`always_comb`/NBA, which together reach
about one file in twenty. The cycle model is not merely incomplete; it
is specialised for the *rarest* shape in the corpus.

### 3.3 THE ACTIONABLE NUMBER: 0.7% → 68.0% in one capability

Nested tiers, each relaxing the previous (a file is "handled" if it
contains none of the out-of-scope groups):

| tier | corpus A | of which have RTL | corpus B |
| --- | ---: | ---: | ---: |
| **T0** strict Active+NBA only (no `initial`, no time, no output tasks, no fork/clocking/assertion/program/class) | **154 (0.7%)** | 15 | 310 (30.0%) |
| T1 = T0 + `$display`/`$finish`/`$stop` | 159 (0.7%) | 19 | 311 (30.1%) |
| T2 = T1 + `initial`/`final` | 8 280 (**38.3%**) | 174 | 667 (64.5%) |
| **T3** = T2 + `#` delays and `always #d` clock-gen | **14 703 (68.0%)** | 2 917 | 685 (66.2%) |

*(T0 = 154 here vs the 171 this section first published; the difference
is comment/string filtering plus the wider file set.)*

**Corpus B's 30% at T0 is inflated and should not be quoted**: 263 of
those 310 files contain no process at all. Only **47 files (4.5%)** are
both T0-clean and contain RTL.

**Items 1-6 of the ranked table are ONE capability — a procedural
process with a time wheel** (`initial` + `#` + standalone `@` +
`$display`/`$finish`). That single addition takes corpus A from **0.7%
to 68.0%**, in two steps worth **+37.6pp** (`initial`) and **+29.7pp**
(delays). Nothing else on the ladder comes close.

> **What the 68% is, and is NOT — two axes, and this table measures one
> of them.** The tiers above are a **scheduling** measure: a file counts
> if its *scheduling constructs* are in scope. It is not a claim that
> 68% of files would run, because a file also has to be in tier on the
> **vocabulary** axis — its expressions, statements and types. Measured
> independently by the committed census, only **806 of 21 186 files
> (3.8%)** extract with **zero `Unsupported` nodes**, and of those only
> **601 are `:type: simulation`** — 3.4% of the 17 856 runnable tests.
>
> So 4a removes the *scheduling* blocker for 68% of the corpus; the
> vocabulary blocker is a separate axis and is what R2's breadth rungs
> address (today's top blockers being signedness and range metadata, not
> exotic constructs). **Total in-tier coverage is gated by both, and no
> claim should quote 68% as a runnability figure.**

The second capability is the **Preponed/Observed/Reactive cluster**
(clocking + concurrent assertions + program blocks), worth roughly
another 15pp — and Preponed 15.2% and Reactive 13.3% are essentially
*one workload*, not two, concentrated in chapters 14/16/17/24/39.

### 3.4 The regions are CHAPTER-LOCAL, which makes staging easy

| chapter | files | concentration |
| --- | ---: | --- |
| **4** (scheduling) | 430 | 85.3% delay, 34.2% NBA, 29.3% standalone `@`, **16.5% `#0`**, **7.7% `$strobe`/`$monitor`** |
| **14** (clocking) | 463 | **100% clocking**, 99.6% standalone `@`, 36.1% NBA |
| **16/17/39** (assertions/checkers) | 2 131 | 84.4% / 79.2% / 93.4% concurrent assertions |
| **24** (programs) | 347 | **98.3% `program`** |
| 9 (processes) | 563 | 38.0% `fork` |
| 8/18 (classes/random) | 1 681 | 99.0% / 81.7% `class`, **~0% scheduling** |
| 40 | 80 | 85% NBA, 85% RTL — the densest RTL chapter |

**Chapter 4 is the only place Inactive and Postponed matter at all**
(`#0` 16.5% vs 1.3% corpus-wide; `$strobe`/`$monitor` 7.7% vs 0.2%).
That is convenient and slightly circular — the chapter that tests the
scheduler is the chapter that exercises its rare regions — but it means
those two regions can be built *for chapter 4* rather than for the
corpus, and scored there.

**Chapters 8 and 18 (1 681 files) need object semantics, not event
regions.** No scheduling work will move them, and ruling §6.3 puts them
in scope — so they are a separate capability that R1 must not be
measured against.

### 3.5 What this re-orders

The charter framed the expensive half of clause 4 as the **reactive**
family. The corpus agrees about cost but inverts the priority:

* **Active + a time wheel is the whole rung.** `initial` (98.8%),
  `$finish` (97.0%) and `$display` (92.7%) are the universal
  self-checking harness — a model that cannot run them cannot run the
  suite, whatever else it supports.
* **NBA, which the cycle model already has, is a 5% region.**
* **Postponed can ship as a write-prohibited no-op** and be right about
  99.8% of the corpus.
* **Inactive is chapter-4-local** at 1.3% corpus-wide.

So inch 4's internal order is settled by measurement: **Active with a
time loop and the output tasks first**, Inactive next (cheap, and
chapter 4 needs it), the reactive cluster last — which is what §7 inch 9
already defers, now with numbers rather than intuition behind it.

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

### 7.0 PRIOR ART: `initial` is ALREADY EXECUTED, in a parallel tier

Found while pricing 4a, and it changes its shape. **`LeanModels/Sv/
SelfCheck.lean` (867 lines) already runs `initial` blocks.** Its
docstring states the contract: single-module designs whose only
processes are `initial` blocks computing at time 0 and printing
`PASS`/`FAIL` via `$display` — with `$display`/`$write`/`$finish`/
`$stop`, string literals, local declarations, `===`/`!==`, `&&`/`||`,
signed comparisons, `Resize` and `Squash2` on top of the M0 vocabulary.
The extractor already emits `{"kind": "Initial", …}` as a real envelope
node; it is `Json.lean`'s **ingester** that maps it to
`Process.unsupported`, because `Ast.Process` has no constructor for it.

**So 4a is not "build `initial` from scratch."** Two things are already
done — executing an `initial` body, and the output tasks — and the
extractor half of inch 8 is largely done for `initial` too.

**What is actually missing is the part neither tier has: the two are
MUTUALLY EXCLUSIVE.** `SelfCheck` refuses any process that is not
`initial`; the M0 cycle core refuses `initial`. A design with both — an
`always_ff` DUT and an `initial` testbench, which is what a runnable
test *is* — runs under neither. **4a's real content is the union**, plus
the time wheel (`#`), which neither tier has: `SelfCheck`'s docstring
says a `#delay` in a body "arrives as `Unsupported` and is loud when
reached."

**The reach today, measured:** 806 files (3.8%) extract with zero
`Unsupported` nodes, of which **601 are `:type: simulation`** — 3.4% of
the 17 856 runnable tests. That is `SelfCheck`'s ceiling, against the
cycle core's 171 scheduling-clean files.

**And a duplication risk this section exists to prevent.** `SelfCheck`
built its own `SExpr`/`SStmt` that *embed* the M0 types as `.m0` leaves
and delegate to `evalExpr`/`execStmt` — a deliberate wrapper, not a
rewrite. 4a must extend that pattern or subsume it, **not invent a third
statement type**. Whether the region semantics absorbs `SelfCheck` or
sits under it is the first design question of inch 4a, and it should be
answered by reading that file rather than by starting fresh.

| inch | deliverable | price |
| ---: | --- | --- |
| 1 | **This document** — region census, determinism boundary, corpus price | LANDED |
| 2 | `Region`, the region-aware oracle, `Slot`/`RegionTrace`, `isCycleFragment`, `cycleOf` — **types only**, no semantics | **LANDED** — `LeanModels/Sv/Regions.lean` |
| 3 | The `cycleOf` stub + the divider statement shape (§6), against today's cycle semantics | **LANDED** — same file |
| **4a** | **`initial` + the TIME WHEEL + `$display`/`$finish`** — a procedural process, `#` delay, standalone `@`, and the two output tasks. **This is the +67pp inch** (§3.3): corpus A goes 0.7% → 68.0% | the bulk of the rung, and the payload |
| 4b | `slotStep` proper: Preponed sample, the Active/Inactive/NBA loop, Postponed as a **write-prohibited no-op** (right about 99.8% of the corpus, §3.5). **Reactive family stubbed, refusing loudly if reached** | structural; mostly wiring 4a into the region ladder |
| 5 | **The adequacy lemma** `cycleOf_runRegion` on the fragment | the hard theorem; the rung's centre |
| 6 | Re-prove the 23 plumbing lemmas against `slotStep`/`runRegion` | mechanical, follows the definition tree |
| 7 | Transfer the 156: rewrite `run` → `cycleOf ∘ runRegion`, re-check `Deterministic` and the `race_blk` witnesses, re-define `⊑@clk` through `cycleOf` | mostly mechanical *given* inch 5 |
| 8 | Extractor + envelope: stop emitting `Process.unsupported` for `initial` and `#`; `language_version` first-class (charter §7.2 retrofit 3) | one function each; **21 envelope regens, gated by `sv_round_trip.py`** |
| 9 | The Preponed/Observed/Reactive cluster for real — clocking blocks, concurrent assertions, program blocks. **One workload, not three** (§3.3), worth ~15pp | a rung of its own; explicitly deferred past R1 |
| — | *(not R1 at all)* Object semantics for chapters 8/18 — 1 681 files, ~0% scheduling constructs. **No scheduling work moves them and R1 must not be scored against them** | a separate capability |

**Inches 2 and 3 are trivially landable now** and are worth landing
before inch 4a, precisely because they let rung A's divider statement be
written in its final form while the semantics is still being built.

**One design change inches 2-3 forced, recorded here rather than in a
commit message.** The inch text said "the **widened** `ScheduleOracle`".
Widening it in place would have changed `choose`'s type and broken every
existing `∀ σ` theorem **at the exact moment none of them could be
re-proved**, because the semantics they would need does not exist until
inch 4. So `RegionOracle` lands as a *new* type beside the old one, with
an embedding `ScheduleOracle.toRegion` and the conservativity proved:

```lean
theorem ScheduleOracle.toRegion_choose (σ : ScheduleOracle) (k : Nat)
    (r : Region) (ready : List Nat) :
    σ.toRegion.choose k r ready = σ.choose k ready := rfl
```

That `rfl` is the design's "the old oracle embeds as `fun k _ ready => …`"
turned into an obligation the compiler checks. The in-place widening
happens at inch 4, when there is something to widen *into*.

The same file also proves the region bookkeeping cannot drift —
`Region.all` really is `Region.core` interleaved with `Region.pli`, by
`decide` — and `RegionOracle.revIn` demonstrates the new expressive
power the region parameter buys: **a schedule that reorders inside one
region and nowhere else**, which the cycle-level oracle could not state
and which region-local race witnesses will need.

**The corpus moved the payload from 4b to 4a.** This document's first
draft put `slotStep` and its region ladder at the centre of the rung.
The filtered census says the region *machinery* is not what buys
coverage — a procedural process with a time wheel and two output tasks
is. `initial` at 98.8%, `$finish` at 97.0% and `$display` at 92.7% are
the suite's universal self-checking harness, and **a model that cannot
run them cannot run the suite whatever else it supports.** 4b is still
required — it is what makes 4a *correct* rather than merely useful, and
it is what the adequacy lemma is stated against — but it is the frame,
not the payload.

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

---
## 9 THE SHARED-MONAD SUBSTRATE — fit census and verdict

The owner asked whether SV can be rewritten onto the shared monad
structure, and then sharpened it: *"target SV's scheduler semantics from
the start when making these decisions, since that will eventually have to
be done."*

**That sharpening closed a loophole this section had already fallen
into.** The first draft censused the fit of `Sv.Res` and of a `W` shaped
for the **cycle model** — and concluded the types were compatible. That
conclusion was true and nearly useless: it validated the substrate
against the **projection** rather than against the **definition**. Under
ruling §6.4 the cycle model is a *view* of clause 4, not a semantics in
its own right, so a `W` designed for it would have to be redesigned at
inch 4b — the second rebuild the ladder exists to avoid.

**So the question is not "does `Sv.Res` map onto the substrate" but
"does the substrate carry the FULL event scheduler".** What follows is
that census.

### 9.1 The gate's own question, answered

*Are the inch 2-3 types substrate-compatible, and scheduler-shaped?*
**Yes to both, measured.** `LeanModels/Sv/Regions.lean` mentions `Res`
zero times and `Monad` zero times (its one `bind` is `Option.bind`), and
what it *does* define is scheduler-shaped by construction: `Region` is
all fifteen of clause 4's regions, `RegionOracle` is the choice-within-a-
region contract, and `cycleOf` is explicitly the **projection**, named as
such. Nothing in it is designed for the cycle model; the cycle model is
what it projects *to*.

### 9.2 The stack, with the SCHEDULER as `W`

`Sv.Res α = ok | timeout | unsupported` **is `Except Loud α` exactly**,
and already carries a `Monad` instance — where Python's `Run σ α` needed
a 22-line iso to reveal its stack, SV's needs less, because M0 SV has no
exception arm to reconcile. That part of the first draft survives.

What changes is `W`. Designed for clause 4 rather than for cycles, the
honest inventory is:

```lean
-- illustrative: the scheduler-shaped World, not in the tree
inductive Trigger where            -- why a process is suspended
  | atEdge  (sig : String) (e : Edge)     -- @(posedge clk)
  | atTime  (t : Nat)                     -- #d, resolved to absolute time
  | atEvent (name : String)               -- named event
  | waitFor (cond : Expr)                 -- wait(expr)

structure ProcState where
  residual : List Stmt        -- THE DEFUNCTIONALIZED CONTINUATION (§9.3)
  status   : ProcStatus       -- ready | suspended Trigger | finished

structure SvWorld where
  time      : Nat                       -- the time wheel's now
  signals   : SvState                   -- the 4-state signal environment
  procs     : Array ProcState           -- the process table
  regionQ   : Region → List Nat         -- ready set per region
  curRegion : Region                    -- the active-region pointer
  nba       : NbaQueue                  -- write-then-commit buffer
  reNba     : NbaQueue                  -- the reactive family's buffer
  future    : List (Nat × Nat)          -- (wake time, proc) — the wheel
  out       : List String               -- $display / $write buffer
  k         : Nat                       -- oracle invocation counter
```

Canonically (`docs/family-architecture.md` §3.4):
`SemM W ρ := ExceptT ρ (StateT W Halt)`, in that order — with `Halt` the
`Except Loud` base. **The order is load-bearing and was corrected there
by `rfl`**: `StateT` *outside* `ExceptT` discards the state on a raise
(`W → Except ρ (α × W)`), where the right order keeps it
(`W → (Except ρ α × W)`). SV needs the right order for the same reason C
does — `$finish` must preserve the output buffer.

| substrate layer | SV instantiation |
| --- | --- |
| `Halt` = `Except Loud` (base) | `Res`'s `timeout` (comb loop / non-convergence) and `unsupported`, both state-discarding — **exists exactly** |
| `StateT W` | `SvWorld` above. Threaded **manually** today, so a `StateT` presentation is a re-presentation; but the *contents* are new, and they are the scheduler's, not the cycle model's |
| `ExceptT ρ` | **empty in M0**, filled by `$finish`/`$stop` |
| the schedule `σ` | **outside**, universally quantified — see §9.4 |

**`$finish` is `ρ`, not `Loud`.** It terminates simulation but the
`out` buffer **is the test's verdict** and must survive; `timeout` and
`unsupported` discard state because nothing meaningful remains. This is
the C tier's `abort`/`exit` distinction, and inverting it would silently
throw away the `PASS`/`FAIL` line that **97%** of the corpus depends on
(§3.1).

**Yes, `W` is big.** That is expected and is not a defect: the substrate
was never meant to shrink the semantics, only to standardise its
plumbing and its proof interface. A stratified event scheduler has a lot
of state because clause 4 says it does.

### 9.3 THE SUSPENSION QUESTION — the family-level one, answered

**This is the question that decides whether the substrate can hold SV at
all.** A SystemVerilog process suspends *mid-body* at `@`, `#` or
`wait`, other processes run, and it later resumes where it stopped. That
is coroutine behaviour, and a `StateT W` computation is
**run-to-completion**: `W → (α × W)` has nowhere to put "paused here".

Stated sharply: **`SemM` as specified cannot suspend.** If a process's
continuation had to be a *monadic value* held across a scheduling point,
the substrate would be the wrong shape and this would be a family-level
finding against the concurrency four-piece pattern.

**It does not have to be, and the escape is defunctionalization.** The
continuation is kept as **data in `W`** — `ProcState.residual`, the
remainder of the process's statement list — rather than as a suspended
computation. The interpreter is then a **scheduler loop over the process
table**:

```lean
-- illustrative
def stepProcess (σ : RegionOracle) (p : Nat) : SvM StepOutcome
  -- runs procs[p].residual until it completes or hits a Trigger;
  -- writes the remaining statements back to procs[p].residual.
  -- SUSPENSION IS A RETURN VALUE, never a monadic effect.

def runRegion (σ : RegionOracle) (r : Region) (fuel : Nat) : SvM Unit
  -- σ orders the ready set for r; step each; iterate to exhaustion.
```

**So the verdict on the family question is: the substrate HOLDS the full
scheduler, with the process table inside `W` and the interpreter as the
scheduler loop over it** — the outcome the dispatch thought likely, now
with the mechanism named. Suspension is representable because it is
*data*, and it is data because SV processes suspend only at syntactically
identifiable points, so the residual is always a statement list.

**The price, stated plainly — and it is one field.** Defunctionalization
means the AST's statement list doubles as the continuation type, which is
cheap; but it also means `stepProcess` is a **second interpreter shape**
over `Stmt` — one that can stop half way — where today's

```lean
def execStmts (fuel : Nat) (st : SvState) (nba : NbaQueue) (ss : List Stmt) :
    Res (SvState × NbaQueue)
```

runs to completion. The resumable form extends that return type by
exactly one field:

```lean
inductive StepOutcome where
  | done
  | suspended (t : Trigger) (residual : List Stmt)

def stepStmts (fuel : Nat) (st : SvState) (nba : NbaQueue) (ss : List Stmt) :
    Res (SvState × NbaQueue × StepOutcome)
```

**The two must not both exist unreconciled**, and the reconciliation is a
lemma of exactly the adequacy shape:

```lean
theorem stepStmts_trigger_free (h : ss.all Stmt.isTriggerFree) :
    stepStmts fuel st nba ss
      = (fun p => (p.1, p.2, .done)) <$> execStmts fuel st nba ss
```

So 4a's `stepProcess` *subsumes* `execStmts` — a process with no trigger
in it **is** the run-to-completion case — which is also the answer to
§7.0's `SelfCheck` duplication risk: one resumable stepper, with the
existing non-resumable one as its trigger-free special case, related by a
theorem rather than by convention.

**One thing this does NOT solve**, flagged rather than buried: `fork`/
`join` (2.9% of the corpus) creates *dynamic* processes, so `procs` must
grow at run time and `join` needs a completion barrier. That is
expressible in the same `W` — a spawned process is another `ProcState` —
but it is not exercised by 4a and its design is deferred to the rung
that needs it.

### 9.4 `σ` stays OUTSIDE, and the scheduler makes that load-bearing

Under the cycle model `∀ σ` was already the doctrine. Under the full
scheduler it becomes the *only* thing standing between the tier and a
false claim, because there are far more scheduling points: every region
of every slot orders its own ready set.

`σ` is therefore a **parameter of the definitions** (`runRegion σ …`),
never a field of `W`. A schedule threaded through the state would become
a choice the program *makes* rather than one quantified *over*, and every
race theorem would change meaning. This matches the family's treatment
of Go's schedule, and it is why `RegionOracle` (landed at inch 2) takes
the region as an argument rather than reading it from a world.

### 9.5 THE SV-SPECIFIC TRAP: `x` is NOT `ρ`

Four-state unknown is a **value**, not an error. `lx`/`lz` flow through
the `LVec` operators by tabulated per-operator rules; they never
short-circuit, and an `x`-carrying result is a **successful** run.

A migration that reached for the `ExceptT` layer to model x-propagation —
a natural-looking move, since "unknown" reads like "exceptional" — would
**destroy the value model**, converting 4-state semantics into
2-state-plus-errors. `ρ` is `$finish` and `$stop`. Nothing else.

### 9.6 What does NOT map: the fuel ladder, 62% of the estate

All 98 proof-carrying declarations, classified by the pilot's
reachability criterion (`docs/mvcgen-pilot.md` §2):

| class | count | share | `mvcgen` |
| --- | ---: | ---: | --- |
| fuel-recursive (`_le`/`_mono` ladder) | **50** | 47% | **outside** |
| ∃-fuel threshold form | **11** | 10% | **outside** |
| trace-shaped, fuel-free | 16 | 15% | reachable in principle |
| statement-shaped | 29 | 27% | **native** |

**62% sits where the pilot measured `mvcgen` returns the goal unchanged
after 1 m 31 s.** `Obs.lean` alone holds 44 of them.

**And SV's fuel is SEMANTIC where Python's is an artifact.**
`Res.timeout` does not mean "the model ran out of budget"; it means
**non-convergence** — a combinational loop today, and under the full
scheduler also a zero-delay loop that never lets time advance. Both are
real, reportable properties of the design under test. The pilot's
Route C (drop fuel, make the loop total by a measure) is therefore **not
available** at `combSettle`, and **still not available** at the region
loop, because non-termination there is exactly what the tier must
detect rather than exclude. The 50-lemma ladder is **intrinsic to the
semantics, not incidental to its encoding.**

*(One route nobody has measured, flagged not assumed: fuel as a **field
of `W`** with `decreasing_by` — distinct from both "fuel as a layer"
(not definable) and "fuel as an argument" (no progress). Under the
scheduler design this is more attractive than it was, because `W` exists
anyway and the loop is already a state machine. Cheap experiment; SV has
the most to gain from the answer.)*

### 9.7 The economic argument: SV has NEVER paid for a walker

| tier | hand-rolled VC machinery |
| --- | ---: |
| Python | `VC` 546 + `VC2` 939 + `VCTactic` 3 371 + `LoopTactic` 487 = **5 343 lines** |
| **SystemVerilog** | **none** — `sv_prove` is a "first-cut tactic" inside a 450-line `Surface.lean` |

SV is exactly pilot §4's case: a tier that has **not paid**, choosing
between ~120 lines of substrate and eventually growing its own walker.
Under ruling §6.6 the surface only grows, so "eventually" is not
hypothetical — and the scheduler is precisely the growth that would
force it.

### 9.8 THE VERDICT: **(b) HYBRID**, with the scheduler as the target

**New code on the substrate, scheduler-shaped from its first commit.
Dormant tier NOT rebuilt. `Res` unified into `Core` because it is free.**

**(a) FULL ADOPTION — priced and DECLINED.** Its rebuild half re-proves
61 fuel-shaped theorems `mvcgen` cannot assist, to reach a presentation
whose benefit sits in the 29 statement-shaped ones — and it would be paid
at the exact moment R1 changes the trace type underneath anyway.
**Rebuilding twice is worse than rebuilding once, and R1 is the rebuild
that has to happen.**

**(c) STATUS QUO — DECLINED.** 4a is new code; there is no reason to
write new code off-substrate, and doing so would forfeit SV's chance to
be the substrate's second real consumer at zero migration price.

**(b) HYBRID — ADOPTED:**

1. **4a's payload is written on the substrate AND scheduler-shaped from
   commit one.** `W` is `SvWorld` as in §9.2 — the process table, the
   per-region ready sets, the time wheel and both NBA buffers — **even
   though 4a's `initial`-blocks-and-delays coverage exercises only part
   of it.** Reserving the structure now is cheap and impossible later;
   it is the family's own precedent (Go's schedule, C's threads).
2. **`Sv.Res` unifies into `Core`** — integration-checklist item 3, of
   which only the `Span` half ever landed (`Core/Basic.lean` is 13 lines
   holding `Span` alone). It is an **iso, not a migration**, and it is
   the landing that makes SV a real `Core` consumer where §7.3's
   correction found the recorded count of 3 was actually **zero**.
3. **The dormant tier is bridged where consumed, not rebuilt.** The 50
   monotonicity lemmas stay; `cycleOf_runRegion` (§5.3) is the bridge and
   is owed regardless of this question.
4. **`mvcgen` on the fuel-free fragment only**, with threshold assembly
   by hand at `combSettle` and the region loop, per the pilot.

**And one finding that went OUTWARD to the architecture lane — not
loudly as a failure but precisely as a constraint. It has since
LANDED there**, as `docs/family-architecture.md` §(1a) *"`SemM` CANNOT
SUSPEND — and the pattern survives only because the process table lives
in W"*, which corrects that document's earlier *"nothing about the monad
changes"* and states the structural fact by `rfl`:
`ExceptT ρ (StateT W Halt) α` unfolds to `W → (Except ρ α × W)` — an
`α`, or a `ρ`, plus a `W`, **and no third case**.

The generalisation the family drew from SV's case is worth reading back
into this lane, because it is the rule 4a must follow: defunctionalization
is **sound because suspension points are SYNTACTIC** — a process pauses
only at a construct the grammar names, so "where it paused" is a position
in the program text and not an arbitrary closure. A language that could
suspend at an arbitrary point would need a real continuation and this
trick would not be available. **The concurrency pattern's
schedule-as-parameter claim survives this test — but it survives
*because* the process table went into the World.**

### 9.9 Consequence for the inch ladder

| inch | change |
| --- | --- |
| 2-3 | **unchanged and LANDED** — substrate-neutral and scheduler-shaped (§9.1) |
| **4a-0** | **NEW**: `SvWorld` **as in §9.2, scheduler-shaped**, the `ExceptT ρ (StateT SvWorld (Except Loud))` presentation, `Res`→`Core`, and `@[spec]` lemmas for the primitives (`readSignal`, `SvState.set`, NBA push/commit, `$display` emit, `$finish`, wheel insert/pop). Est. **~120 lines** of substrate per pilot §4, plus the `W` declaration itself |
| 4a | `initial` + time wheel + output tasks, written against 4a-0 — and `stepProcess` **subsumes** `execStmts` rather than duplicating it (§9.3, §7.0) |
| 4b-9 | unchanged in content; the region ladder is state-shaped and rides `W` |

**What this does NOT decide**: whether the fuel-in-`W` route is
`mvcgen`-walkable (§9.6), and how `fork`/`join`'s dynamic process
creation is scheduled (§9.3). Neither is on R1's critical path.

### 9.11 THE STATEMENT TYPE — three candidates, and the answer is EXTEND, not invent

Pricing 4a's stepper turned up a fact that changes its first move.
**`Ast.Stmt` has no suspending constructor and cannot get one.** Its five
cases are `blockingAssign`, `nbaAssign`, `ifStmt`, `block`,
`unsupported` — `@`, `#` and `wait` all arrive as `.unsupported` today —
and it is a closed inductive that the M0 interpreter and its proofs
**match exhaustively**, so adding cases breaks every match and every
proof at once.

That is precisely why `SelfCheck` did not add any: it wraps instead,
with `SStmt` embedding M0 as `.m0` leaves. So there are three candidate
statement types in play, which is one more than §7.0 warned about:

| type | has | missing for 4a |
| --- | --- | --- |
| `Ast.Stmt` | the M0 five | everything; **cannot be extended** |
| `SelfCheck.SStmt` | `.m0`, `.assign`, `.ifStmt`, `.block`, `.localDecl`, **`.sysCall`** (`$display`/`$write`), **`.finish`**, `.skip` | the three **suspension** forms |
| a new `RStmt` | — | **would be the third type; do not write it** |

**The extend-versus-wrap choice is settled by MEASUREMENT, and the
asymmetry is the whole point.** The argument that killed extending
`Ast.Stmt` — "matched exhaustively by the interpreter and its proofs" —
does **not** transfer to `SStmt`:

| | `Ast.Stmt` | `SelfCheck.SStmt` |
| --- | --- | --- |
| files that mention it | interpreter + proofs + examples | **1** (`SelfCheck.lean`) |
| proof-carrying declarations over it | part of the **156** trace-shaped estate | **0** |
| match arms to update | the M0 interpreter and every exhaustive proof | **22**, all in that one file |
| executable `#guard`s | — | 50, none exercising new cases |

**Extending `Stmt` is catastrophic; extending `SStmt` is one file with no
proofs to re-prove.** So the answer is to EXTEND `SStmt` with the
suspension constructors, not to invent a third type:

```lean
-- illustrative: the three cases 4a adds to SStmt
  | delay     (amount : Nat)                    -- #d
  | waitEvent (sig : String) (e : Edge)         -- @(posedge clk)
  | waitCond  (cond : SExpr)                    -- wait(expr)
```

**This is strictly better than the `RStmt` sketch §9.3 implied**, because
`SStmt` *already carries the two things 4a needs most*: `.sysCall` is
`$display`/`$write` — **92.7%** of the corpus — and `.finish` is
`$finish`/`$stop` at **97.0%**. Inventing `RStmt` would have meant
re-deriving both.

**And `ρ` already exists in the tier, hand-rolled.** `SelfCheck`
executes `$finish` as

```lean
| .finish => .ok (st, nba, { out with halted := true })
```

— **`.ok`, not a failure, with the output preserved and a `halted` flag
that downstream execution short-circuits on.** That is `ExceptT ρ`
**defunctionalized into the state**, arrived at independently a month
before the substrate was specified. It confirms §9.2's layer argument
from inside the tier rather than by analogy with C: `$finish` must
preserve `out`, and the existing code already makes sure it does.

**So the migration has a concrete, small first target**: replace the
hand-rolled `halted` flag and its short-circuit with the `ExceptT ρ`
layer, which is one `@[spec]` lemma and deletes a manual check from
every statement case. That is a genuine simplification, not a
re-presentation — and it is the smallest possible demonstration that the
substrate earns its place in this tier.

**Revised first move for 4a** (superseding §9.9's ordering of 4a-0):

1. extend `SStmt` with `delay`/`waitEvent`/`waitCond`;
2. `stepSStmts` returning `… × StepOutcome`, with `execSStmts` recovered
   as the non-suspending case by the adequacy-shaped lemma;
3. `SvWorld` + the scheduler loop;
4. adopt `Core`'s `SemM` spelling when the extraction lands (§9.10),
   replacing `Out.halted` with the `ExceptT` layer at that point.

### 9.10 THE GATE ON 4a-0: `SemM` is NOT IN THE TREE, and SV must not race it

Checked today: `LeanModels/Core/` contains **`Basic.lean` alone**, and
`grep -rn 'SemM' LeanModels/` returns **nothing**. `SemM` exists as a
*specification* in `docs/family-architecture.md` §3.4 and as work "in
flight" in the rebuild lane.

**This turns 4a-0 into a coordination point rather than a coding task**,
because the family document states the rule that governs it:

> *"a second interpreter landing with its own copy of `Run` is a defect,
> not a design"*

and collapses two landings into one:

> *"'move `Run` to `Core`' and 'land the `SemM` substrate' are the same
> landing, not two. The destination should therefore be the stack, with
> `Run` as its established view."*

So **4a-0 must not define an SV-local copy of the stack.** Three
candidates are named for who triggers the `Core` landing — C's M2 inch 4,
the rebuild lane's `SemM`, or a third tier adopting the outcome type —
and *"whichever lands first is the trigger."* SV's 4a-0 is exactly such a
tier, which leaves two honest options:

* **(i) WAIT** for the rebuild lane's `SemM`, and write 4a-0 against it.
  4a's `SvWorld` and its `@[spec]` lemmas are SV-local and unaffected;
  only the stack's *definition* is shared. This is the default.
* **(ii) BE the trigger** — SV lands `SemM` into `Core` itself, with
  `Run` as its established view. This is a **family-level landing that
  touches Python's 1 282 `Run.` sites across 31 files**, and the rebuild
  lane is already in flight on it, so taking it unilaterally would be a
  race, not a contribution.

**Recommendation: (i), and it costs R1 nothing.** Inches 2-3 are landed
and substrate-neutral; 4a's own content — `SvWorld`, `stepProcess`, the
time wheel, the region loop — is SV-local and can be written against a
stack that arrives later, since the only coupling is which `abbrev` the
monad is spelled with. **What must NOT happen is 4a-0 quietly defining
`SvM := ExceptT ρ (StateT SvWorld (Except Loud))` locally** — that is
precisely the "own copy" the family rule names as a defect, and it would
be discovered later as drift rather than now as a dependency.
