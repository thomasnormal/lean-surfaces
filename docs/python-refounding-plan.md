# Re-founding the Python tier on the monadic interpreter — the retirement census

**Thomas's ruling** (2026-08-22): *"Yes, please merge. Keep only the new
versions, no reason to be backwards compatible on anything."*

The rebuild passed the acceptance gate (1394/1394 closed-function parity, zero
divergences, script corpus identical row-for-row). Under "no compat" the
question is no longer *whether* the trunk interpreter retires but *in what order
its consumers move*. **This document is a PLAN and a MEASUREMENT. It changes no
Lean.**

---

## §1 THE CENSUS — what actually depends on the old interpreter

### 1.1 The tier layer (`LeanModels/Python/`)

| file | lines | theorems | role |
|---|---:|---:|---|
| `Semantics.lean` | 6684 | 20 | THE INTERPRETER — the statement target of everything below |
| `PayloadBlind.lean` | 3922 | 113 | meta-theorems over the interpreter |
| `VCTactic.lean` | 3371 | 30 | **the walker** (`py_vcgen`, `py_loop`) |
| `Obs.lean` | 3119 | 75 | observation/erasure meta-theory |
| `ClockErase.lean` | 2732 | 70 | the clock-erasure meta-theorem |
| `VCGen.lean` | 2034 | 95 | VC generation |
| `Json.lean` | 1660 | 0 | INGESTION — shared, not interpreter-specific |
| `Runtime.lean` | 1317 | 26 | `RVal`/`World`/`Run` — shared |
| `VC2.lean` | 939 | 27 | triple layer |
| `Surface.lean` | 930 | 24 | the typed spec surface |
| `Script.lean` | 893 | 0 | script admissions — **530 lines already reused** |
| `DictCalc.lean` | 825 | 43 | dict calculation lemmas |
| `VC.lean` | 546 | 26 | `PyTriple` |
| `LoopTactic.lean` | 487 | 1 | loop tactic |
| others | ~2000 | ~40 | Ast/Logic/ModuleInit/Delab/Tests |

**~32 400 lines, ~591 theorems.**

### 1.2 The campaign estate (`Examples/python/`)

**35 385 lines, 1 357 theorems**, of which `sunfish/` is **25 063 lines and 929
theorems** — the flagship. Its largest files: `bound_depth` (4356/221),
`genmoves_ray` (3740/174), `basecase_depth0` (2422/54), `fold_depth1`
(2178/55), `move_gate` (2090/163), `value_bound` (1765/57).

### 1.3 Coupling, measured by symbol

| symbol | files |
|---|---:|
| `#py_check` | 63 |
| `py_simp` | 42 |
| `CallsTo` | 39 |
| `CallsIn` | 23 |
| `py_vcgen` | 22 |
| `py_loop` | 18 |
| `PyTriple` | 8 |
| fuel-family forms (`∃ t, ∀ F ≥ t`, `fuelMono`, `_at_least`) | **13** |

**The load-bearing number is the last one: only 13 files state fuel-family
claims.** Those are the ones whose SHAPE changes, because the rebuild's fuel
boundary is different — everything else is a statement about values and worlds
that the monadic interpreter answers identically (that is what 1394/1394 means).

---

## §2 CLASSIFICATION

**(a) RE-PROVE on the monadic interpreter** — value/world claims on the
fuel-free fragment. `mvcgen` + `@[spec]` + `grind` make these cheap per gate:
the closing script is often *deleted outright* (measured on two gates). This is
the large majority by file count.

**Caveat, measured and not to be forgotten:** the four-deep `value_scores` shape
does **not** close even with `grind`, because the blowup is in `mvcgen`'s own
splitting, not in discharge, and the altitude lemma that would fix it cannot be
stated (the splitter drops the discriminant). **So (a) is cheap per gate but has
a known ceiling on statement depth.** Deep gates fall back to hand proof, and
that cost must be in every estimate.

**(b) RESTATE** — the 13 fuel-family files. `∃ t, ∀ F ≥ t` is outside the WP
layer by construction (`Triple` is unary on one program; these are claims about
a *family*). They are hand-proved against the NEW interpreter's fuel structure,
and that structure genuinely differs: fuel is spent only at `Kont`'s boundary,
so a claim that counted per-node decrements is not merely re-typed, it is
re-derived. **These are the expensive ones and they cannot be transported.**

**(c) — AND THIS SECTION WAS WRONG TWICE, in opposite directions.**

The first draft said `VCTactic` (3371), `LoopTactic` (487) and `VCGen` (2034) could be
"deleted immediately, no successor". The second draft withdrew that on a
consumer count. **Both were confused, because they treated tactic files and
predicate files as one class.** Thomas's correction is the distinction that
makes the section true:

> **A tactic can only appear in a PROOF, never in a theorem STATEMENT.**

That single fact splits (c) cleanly, and the halves have nothing in common.

### (c1) THE TACTIC FILES — zero semantic weight

`VCTactic.lean` (3371, exports `py_vcgen`) and `LoopTactic.lean` (487, exports
`py_loop`/`py_begin`). Their 17 / 14 / 11 consumers are **proof sites**, and
under the ruling those proofs are being rewritten anyway.

**These files carry no meaning.** They are LIBRARY in §0.1's sense — untrusted
by doctrine, producing proofs the kernel rechecks against a definition they
cannot influence. Deleting them cannot make any statement weaker or any theorem
false; it can only make a proof fail to compile.

**So the only reason not to delete them today is `master`-never-red — not loss
of meaning**, and that is the whole of it. They retire **file-by-file with the
old proofs they serve**, and the last one to go takes the file with it. Nothing
here needs designing, only sequencing.

### (c2) THE PREDICATE FILE — re-founded, and some words REPLACED

`VCGen.lean`'s predicates *are* statement vocabulary (`PyStmtTriple` 10 files,
`IterSteps` 10, `GenEmits` 10, `IterDrains` 8). But they do not survive
unchanged either, and the reason is visible in every one of their definitions:

**every one is the ∃-threshold form over the OLD interpreter's run relation** —
`∃ t, ∀ F ≥ t, <old interpreter …> = …`. They are not neutral vocabulary that
happens to be used with the trunk; they are *defined by* it. So each is either
re-founded over the monadic interpreter or replaced by a core word that already
says it.

**Per-predicate disposition:**

| predicate | defined over | disposition |
|---|---|---|
| `PyTriple` | `execStmts m F` | **REPLACE** with core `Std.Do.Triple` — the pilot showed it is a hand-rolled stand-in |
| `PyStmtTriple` | `execStmt m F` | **REPLACE** — same, one level down |
| `PyPost` | `Run FrameState RFlow` | **REPLACE** with core `PostCond`; the five flow arms ride the success barrel as a sum (`Spec.repeatM`'s own idiom) |
| `EvalsTo` | `evalExpr m fuel` | **REPLACE, and it gets STRICTLY simpler** — `evalOpen` is fuel-free, so this becomes a plain `Triple` with **no threshold at all** |
| `EvalsIn` | `evalExpr m F` | **REPLACE** — same, with the state threaded |
| `IterSteps` | `stepIter m F` | **RE-DEFINE** over `K.stepIter` — no core equivalent |
| `IterDrains` | `drainIter m F` | **RE-DEFINE** over `K.drainIter` |
| `GenSteps` | `execGen m F` | **RE-DEFINE** over `K.execGen` |
| `GenYields` / `GenYieldsPrefix` | `drainGen` / `stepGenN` | **RE-DEFINE** over the new stepper |
| `GenSilent` | `execGen m (F + d)` | **RE-DEFINE, and its SHAPE moves most.** Its entire content is composing FUEL OFFSETS, and the rebuild spends fuel once per `Kont` level rather than per interpreter step |
| `GenEmits` (GenBound) | frame-prefix emission | **RE-DEFINE** over the new generator step |

**Five replace, six re-define, and zero preserve.**

**The replacements are a trust win, not just tidying.** Every hand-rolled word
removed from a STATEMENT is one fewer definition a reader must audit before
believing a theorem. `PyTriple` was a stand-in for `Std.Do.Triple`; saying so in
core's vocabulary means the statement's meaning is fixed by Lean's own library
rather than by 546 lines of ours. §0.1's trust boundary is drawn at the
DEFINITION, so shrinking the definition layer is the one kind of simplification
that is also a soundness argument.

**And `EvalsTo` is the shape of the whole win.** It is currently a threshold
claim because the trunk charges fuel per expression node; on the rebuild,
expression evaluation is fuel-free and structural, so the *same fact* is stated
without a fuel quantifier. That is the fuel-boundary ruling paying out in the
statement layer, not just the interpreter.

**SHARED — not retiring at all**: `Ast`, `Json`, `Runtime`, `Surface`,
`Script`'s admissions, `DictCalc`. The rebuild already imports these; they were
never interpreter-specific. This is the maximal-trunk instinct paying at
retirement time.

---

## §2.5 THE ARCHAEOLOGY — harvest before (c1) deletes

Retiring a tactic layer risks losing ideas that took a campaign to find. So the
three files were swept mechanism by mechanism before any deletion. **Two
findings changed the premise of the exercise itself.**

### 2.5.1 THE NAMED TRICKS ARE NOT IN THE FILES BEING DELETED

The harvest was scoped from a ledger of named tricks. Measured, they are almost
entirely somewhere else:

| named trick | in the 3 retiring files | in `Examples/python/sunfish/*` + `backlog.md` |
|---|---:|---:|
| "altitude" | 6 | **44** |
| "exit law" | 0 | **33** |
| "PstAt" | 0 | **58** |
| "two gates" | 0 | **14** |
| "DRAIN" (short-circuit) | 2 | **12** |

**They live in the PROOFS and the record, not in the walker.** That is the
natural place for them — they are *statement-and-proof* disciplines, and a
tactic file is neither. So **(c1)'s deletion loses none of them**, and the
harvest's real subject is the machinery the sweep found instead.

One de-confliction: `DRAIN` occurs in `VCGen.lean` 47 times meaning *generator*
drain (`drainGen`/`drainIter`), which is an unrelated notion from the
short-circuit DRAIN trick. Counting the lowercase name would have "confirmed"
the trick was there.

### 2.5.2 `VCGen.lean` IS NOT VC GENERATION

Its header: *"The generator tier (`py_vcgen` layer 2G) … Layers 1 and 2
(VC.lean, VC2.lean) specify STATEMENTS … This file specifies SUSPENDED
MACHINES."* Earlier drafts of this plan called it "VCGen's generation half" and
were simply wrong about what the file is. The VC *rules* are in `VC.lean` /
`VC2.lean`; `VCGen.lean` is the generator calculus — which is why its predicates
are `GenYields` / `IterDrains` and why they need re-definition over the new
stepper rather than replacement by a core word.

### 2.5.3 THE INVENTORY, classified

**(A) ALREADY PRESENT in the monadic route — harvest nothing, note the
convergence.** `(dec := …)`/`(inv := …)` ↔ `WhileVariant`/`WhileInvariant`
(the pilot measured this one-to-one). Two-gates-per-`if` ↔ `mvcgen`'s own split,
which hands each arm its guard already in context. Straight-line chunking ↔
`mvcgen` walking a `do` block natively. Computed-shape closers ↔ still needed,
though `grind` now closes many of them.

**(B) GENERALIZABLE — worth a home outside this lane.** These are the harvest.

| mechanism | the idea, language-free |
|---|---|
| named-telescope clause goals | a function-typed goal is consumed POSITIONALLY and silently cross-wires binders; introduce the telescope so there is no order to get wrong — and introduce it AFTER the walk, because a delayed-assigned mvar leaks to the kernel |
| discharger **+** condition-deciding simproc | simp asks a discharger only about conditional-rewrite hypotheses; an `ite` CONDITION needs arithmetic *inside* the set. Both halves or neither |
| side conditions in the discharger's vocabulary | phrase a lemma's side condition over the ORIGINAL variable, not a derived term, or the discharger cannot reach it from the invariant |
| frame-stack polymorphism | state every rule over `pre ++ k` with `k` free; composition is then literal `List.append` |
| re-observe, don't frame | demand a FRESH per-round observation instead of a `WritesAvoid`-style stability side condition — a body that clobbers the slot simply cannot re-establish the invariant |
| `Inv [] = False` | one loop rule covers finite AND infinite consumers, because an unsatisfiable empty-remainder invariant discharges exhaustion vacuously |
| one interpreter-wide locality theorem | hoist a repeated frame condition into a single censused property instead of a side condition per rule |
| inversion for threshold-DEFINED judgments | a `∃ t, ∀ F ≥ t` predicate is a definition, not an inductive, so consumers cannot `cases` it — supply `uncons`/`exhausts` or whole-drain specs are unusable |
| unbranding before `omega`/`grind` | reducible abbreviations are transparent to defeq but OPAQUE to syntactic atom matching, so branded hypotheses are silently invisible |
| one hypothesis per conjunct | `grind`'s e-matching instantiates from atoms, not conjunctions |
| match specs modulo the NORMALIZER | a marshalled argument never matches by defeq; compare normal forms |
| read structure fields by NAME | `py_vcgen` read a body at positional field 5, then 6 when a field was inserted — it cost the tier twice |
| dispatchers IN the simp set, workers OUT | the free-scrutinee PLAN resolves the fork; the pure WORKER stays out so proofs rewrite through kernel `rfl` facts |

**(C) PYTHON-SPECIFIC — dies with the tier.** The ~150-name `interpUnfolds`
list; `envInt`; thaw-inversion-by-freezing; `EnvShape`'s `RVal`/`Env` instance
(though "known prefix + symbolic tail" is itself a (B) idea).

**(D) TRAPS — record, do not port.** `omega` is not goal-directed and *silently
proves nothing* on a bare goal. A simproc is keyed by ELABORATED type, so an
unascribed `_ < _` binds at `Nat` and never matches `Int`. Arithmetic simprocs
must be gated or they blow the step budget. The full simp set migrates `!`
across an equation and destroys Miller patterns. Beta-variant types containing
opaque flex applications are not `isDefEq`-decidable. Same-tag goals are
silently consumed by `case`.

### 2.5.4 THE ONE SUPERSESSION, and it is the most valuable datum here

`py_loop` derived its test-value function by **Miller-pattern unification**, and
recorded the two shapes that destroy it: a destructured state variable, and a
surviving `ite`. `py_vcgen` then replaced that with **symbolic evaluation of the
test at the invariant shape** — no unification, no fragility.

**A tier that harvests only the first trick inherits a known-fragile
mechanism.** This is the one place the archaeology must carry the *verdict*
rather than the technique: where two generations of a trick exist, port the
successor and record the predecessor as the thing it fixed.

## §2.6 THE SPEC-HALF / INTERPRETER-HALF SPLIT — 65 % OF THE ESTATE DOES NOT MOVE

The calmness lane's §L30 clean-edge report supplies the datum that resizes this
whole plan, and it is checkable, so it was checked rather than taken.

**Their claim:** their spec half — `foldFrom`, `Report`, `Sound`, `QSRoundOK`,
`fold_report_cut`, `qsRank` and F1's measure calculus — mentions **no
interpreter**. Verified: all six named symbols have **zero** interpreter
mentions in their signatures.

**Measured across the whole sunfish estate**, classifying each theorem by
whether its STATEMENT (not its proof) mentions `execStmt`/`evalExpr`/`CallsTo`/
`CallsIn`/`GenEmits`/`callIn`/`PyTriple`/`∃ t, ∀ …`:

| file | theorems | mathematics | interpreter-facing |
|---|---:|---:|---:|
| `bound_depth.lean` | 221 | **164** | 57 |
| `genmoves_ray.lean` | 174 | 92 | **82** |
| `move_gate.lean` | 163 | **102** | 61 |
| `order_genexp.lean` | 60 | 37 | 23 |
| `value_bound.lean` | 57 | 29 | 28 |
| `basecase_depth0.lean` | 54 | 28 | 26 |
| `fold_depth1.lean` | 54 | 32 | 22 |
| `genmoves_scan.lean` | 42 | 25 | 17 |
| `qs_measure.lean` | 37 | **37** | **0** |
| `move_residue.lean` | 20 | **20** | **0** |
| `genmoves_theorem.lean` | 20 | 16 | 4 |
| `init_chain.lean` | 10 | **10** | **0** |
| `qs_rank.lean` | 7 | **7** | **0** |
| others | 30 | 16 | 14 |
| **TOTAL** | **949** | **615 (65 %)** | **334 (35 %)** |

**Two thirds of the flagship estate is mathematics about `Round` lists,
strings and measures. It survives the re-founding UNCHANGED — it does not need
re-proving, transporting, or even reading.** Four files are 100 % mathematics
and re-found to nothing at all.

### What this changes

**The re-founding scope is 334 theorems, not 949.** Every earlier estimate in
this document — including §3's "671 theorems in four files" — silently counted
statements that never mention an interpreter. The corrected figures for the big
files: `bound_depth` 57, `genmoves_ray` 82, `move_gate` 61 — **200
interpreter-facing theorems across the three, not 558.**

**It re-scopes the `twinAgrees` question too**, in the direction of not needing
it. Transport is only ever needed for the interpreter-facing third; the other
two thirds recompile. A transport tool amortised over 200 theorems is a much
weaker proposition than one amortised over 558.

**And it sharpens §5's spike.** The deep gate to spike must be an
INTERPRETER-FACING one, because those are the only statements whose shape
changes. `genmoves_ray` is the right subject — at 82/174 it is the most
interpreter-facing large file in the estate, so it is where the ceiling bites
hardest.

**The generalisable lesson, which is this repository's own doctrine arriving
from the other direction:** a proof estate that separates its spec half from its
interpreter half is *cheap to re-found*, and one that interleaves them is not.
The calmness lane's split was made for proof-engineering reasons long before a
rebuild existed; it is now worth **two thirds of the migration cost**. That is
an argument for the discipline in every tier, stated as a number.

## §3 `twinAgrees` — NOT a bridge, possibly a TRANSPORT TOOL

Under "no compat" `twinAgrees` is explicitly **not** a compatibility layer to
maintain. But it may still be the cheapest way to move large GREEN files:
prove adequacy once, transport every theorem in a file mechanically, then delete
the old file *and the adequacy theorem with it*.

**The price comparison, per file:**

* **Direct re-proof** costs one `mvcgen` invocation per theorem, cheap on the
  fuel-free fragment and unbounded on deep ones (§2's ceiling).
* **Transport** costs `twinAgrees` **once** — a whole-interpreter induction,
  the genuinely hard artifact — and then near-zero per theorem.

**The crossover is roughly "does one file carry more than ~100 theorems of
mostly-mechanical value-claims".** A first pass named four files on RAW counts —
`bound_depth` (221), `genmoves_ray` (174), `move_gate` (163), `PayloadBlind`
(113), "671 theorems". **§2.6 retires that figure**: counting only
INTERPRETER-FACING statements, the three sunfish files carry **57, 82 and 61 —
200, not 558.** No file clears ~100 on the corrected count, which weakens the
case for transport considerably.

**Recommendation: decide `twinAgrees` on those four alone.** If they re-prove
cheaply in a spike, skip it entirely; if they resist, `twinAgrees` pays for
itself there and nowhere else. **Do not start it speculatively** — it is on
nobody's critical path now that the gate has passed without it.

---

## §4 SEQUENCING — the in-flight lanes decide this, not the census

Two lanes have live inches stated against the old interpreter:

* **calmness / F3c** — `qs_stream.lean` (258 lines, 8 theorems), inch 1 just
  landed.
* **R-track / R3c** — `value_bound` / `fold_depth1` / `order_genexp` /
  `genmoves_drain`, all touched today.

**The price of finishing on the old interpreter vs switching now:**

`qs_stream` is **small and early** (8 theorems, one inch in). Switching F3c now
costs re-stating 8 theorems; finishing on the old one and switching later costs
re-stating however many F3c ends with — and F3c's siblings suggest that is
50–200. **F3c should switch now**; it is the cheapest switch available and it
gets the first real campaign inch written on the new interpreter.

R3c is **mid-inch across four files** with `value_bound` (57) and `fold_depth1`
(55) already deep. **R3c should finish its current inch on the old interpreter**
and switch at the inch boundary — switching mid-inch pays the re-statement cost
*and* loses the inch's context, which is the worst of both.

---

## §4.5 THE SPIKE TICKET — four measurements, and what is already known

Upgraded from `docs/proof-framework-research.md` §9. Three are cheap; all four
share one ticket and run as dependency-free scratch files.

### Already established by READING (no ticket needed)

**`Std/Internal/Do/` is real and it is 17 files** at the pin —
`WP/Frame.lean`, `WP/Conjunctive.lean`, `Order/PreservesSup.lean`,
`Triple/{Basic,Gadget,SpecLemmas}.lean` and the rest. `WPMonad.of_frameClosure`
and `WP.Frames.of_wp_conjunctive` exist as documented. **`Std.Internal` is
explicitly internal and will move — that is a first-class supply-chain finding,
not a footnote**, and it must be priced exactly as the pilot priced `mvcgen`'s
experimental warning.

**A `vcgen` tactic is declared** (`Std/Tactic/Do/Syntax.lean:464`) and its
grammar carries every clause §9 names: `until <term>`, `frames <alt>+`,
`invariantAlts`, `simplifying_assumptions`, and `with <grind-step>` — the last
documented as *"a single `grind`-mode tactic … so it can share `vcgen`'s
internalised E-graph"*. That is the grind seam **built into the tactic** rather
than wired by a `macro_rules` line.

**`jp` defaults to `false`** (`Syntax.lean:43`), so **no measurement this lane
has ever recorded used the linear encoding.** Core's docstring, verbatim:

> *"If `false` (the default), then we aggressively split `if` and `match`
> statements and inline join points unconditionally. For some programs this
> causes exponential blowup of VCs. Set this flag to choose a more conservative
> (but slightly lossy) encoding that traverses every join point only once and
> yields a formula the size of which is linear in the number of control flow
> splits."*

**That is this gate's failure mode named exactly.** It died with `timeout at
whnf` *inside mvcgen's splitting*, and `evalOpen`'s `.name` arm is a nine-way
`match` nested four deep — the precise shape "aggressively split `match`
statements" blows up on. The prior that `+jp` helps should be high.

**Provenance rule adopted: every VC number from now on records its `jp`
setting.** §5.4a says a number carries the state it was measured in, and a
tactic option is part of that state. Both of this lane's recorded ceilings —
the four-deep timeout and the `⊢ False` unstateable lemma — are hereby marked
*measured at `jp := false`* and are not evidence about the linear encoding.

### §4.5.1 A CORRECTION TO THE PROBE SUBJECT

§9 proposes `star_lab/spec.lean` for the Leroy–Grall probe. Measured, the
fuel-family plumbing is far thinner than "13 files" suggests — **~68 sites in
total**, distributed:

| file | lines | plumbing sites |
|---|---:|---:|
| `sunfish/genmoves_ray.lean` | 3740 | **20** |
| `gen_lab/proof.lean` | 1220 | 9 |
| `sunfish/genmoves_theorem.lean` | 563 | **8** |
| `sunfish/value_bound.lean` | 1765 | 7 |
| `sunfish/move_gate.lean` | 2090 | 6 |
| `bench_bisect/proof.lean` | 944 | 5 |
| … | | 3, 3, 2, 2, 2 |
| `star_lab/spec.lean` | 102 | **1** |

**`star_lab` is the worst available probe: it has ONE site.** A probe there
answers "did the single site go away" — 0 % or 100 %, with n = 1 — which cannot
measure *the fraction of plumbing a collapse deletes*, the number the probe
exists to produce.

**Probe `genmoves_theorem.lean` instead**: 8 sites in 563 lines is enough signal
to give a fraction, and still small enough to redo if the collapse needs a
different shape. `genmoves_ray` (20 sites) is the eventual payoff and the right
*second* subject, not the first.

## §5 TOP-3 RECOMMENDATION

1. **Switch F3c to the monadic interpreter now.** Smallest in-flight surface (8
   theorems), and it makes the next campaign inch the first one *founded* on the
   new interpreter rather than transported to it. This is the sequencing
   decision with the shortest half-life — it gets more expensive every day.
2. **Mark the layer LEGACY, and split (c) by the tactic/predicate line.**
   Deletion today is blocked only by `master`-never-red, and only for (c1) —
   whose files carry **zero semantic weight**, so their retirement is pure
   sequencing behind the proofs they serve. (c2) is the half that needs design,
   and §2 now carries the per-predicate table: **five replaced by core words,
   six re-defined, zero preserved.** Do the five REPLACEMENTS early even so —
   they shrink the trusted definition layer, which is a soundness argument and
   not merely tidying.
3. **Spike ONE deep INTERPRETER-FACING gate before committing to a plan for the
   big files** — §2.6 makes the qualifier load-bearing, since two thirds of the
   estate never mentions an interpreter and cannot exercise the ceiling.
   `genmoves_ray` (82 of 174 interpreter-facing) is the subject. The
   §2 ceiling is the plan's only real unknown: if `bound_depth`-scale statements
   re-prove under `mvcgen`+`grind`, the whole estate is class (a) and
   `twinAgrees` is never needed; if they do not, `twinAgrees` becomes the
   central artifact for **334 theorems — not 671.** **Everything else in this
   document is already measured; this is the one number that is not.** Spike it
   before sequencing the remaining ~1 000 theorems.

   > **CORRECTED, and the correction was already in this file — twice.** §2.6
   > retires "671 theorems in four files" explicitly (*"§2.6 retires that
   > figure"*, and again at §2.6's own "including §3's '671 theorems in four
   > files'"), because 671 counted every theorem in those files while only the
   > **interpreter-facing** third can exercise the ceiling at all. This
   > recommendation was written against the pre-§2.6 count and never updated,
   > so the document argued with itself: it retired a figure in one section and
   > priced its top recommendation with it in another. **A number retired in
   > one section is not retired until every section that spends it is
   > re-read** — the provenance law (§5.4a) pointed at a document rather than
   > at a measurement.

---

## §6 WHAT THIS DOCUMENT DOES NOT DECIDE

* When the trunk interpreter's FILES are deleted. They stay while ~15 k lines of
  campaign theorems are stated against them, marked LEGACY with no new
  consumers.
* Whether `twinAgrees` is built — §3 makes that conditional on one spike.
* The re-founding order beyond the top three; the buckets will re-rank once the
  spike lands, and ranking before measuring is the error this repository names
  most often.
