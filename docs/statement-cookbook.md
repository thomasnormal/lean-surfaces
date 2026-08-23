# The STATEMENT COOKBOOK — one page per claim shape

A proof that closes is not the same as a claim that means something. Every
entry below is a shape this repository got **wrong first**, in a way that
type-checked, and the incident that minted the rule is named. Nothing here is
advice: it is a record.

Read it the way you would read a recipe — before you write the statement, not
after the proof fails. Three lines each: **the form**, **the trap**, **the
incident**.

> §0.1 II(a) is the law behind all of them: a statement-elaboration failure
> prints *"does not depend on any axioms"* — **cleaner than the truth**. A
> wrong statement does not announce itself. That is why the shapes are
> written down instead of rediscovered.

| # | shape | the one-line rule |
| --- | --- | --- |
| 1 | determinism / agreement | index it by the OBSERVATION, premise it, never claim it tier-wide |
| 2 | membership sites | membership, never `⊕` — permission is not obligation |
| 3 | ∀-schedule vs witness | MATCH is `□`, DIVERGE-with-witness is a **Lisbon** triple, not an IL one |
| 4 | fold invariants | one direction of a boundary, never both |
| 5 | fuel | a PARAMETER with monotonicity — never a numeral in a hypothesis |
| 6 | spec half vs interpreter half | the proof's vocabulary is free; the STATEMENT's is not |
| 7 | specs for primitives | output-determined: bind the answer in the RESULT |
| 8 | refusals | a named primitive with its own spec lemma, never a bare `throw` |
| 9 | frame predicates | name what the WORLD contributes |
| 10 | threshold judgments | the inverses are theorems, not `cases` |
| 11 | well-formedness | never quantify over what the shipped code constrains |
| 12 | partial correctness | the strengthened form, or it is vacuous for every value |
| 13 | short-circuits | the unevaluated world goes in NO conclusion |
| 14 | gate premises | spell them the way the tactic's residue leaves them |
| 15 | existentials | earned across theorems, not within one |
| 16 | read-only primitives | say the state is unchanged; `Triple` does not frame it |
| 17 | definitions | if a LEMMA cannot state it, the definition moves |
| 18 | refinement | a function-valued projection, and refinement is ∀∃ |
| 19 | refusal causes | the ∀/∃ direction is what distinguishes them |
| 20 | invariant shape | a flat `∧`-chain, at the COMPOSABLE altitude |
| 21 | re-proving | never repair a statement to make a proof pass |
| 22 | opening the monad stack | ONCE, where the stack is DEFINED — and only a STACK needs one |

---

## 1 — Determinism and agreement claims

**FORM.** Index by the observation, and carry the premise:

```lean
theorem det (d : Design) (h : RaceFree d) :
    ∀ σ₁ σ₂ fuel stim, obs (run d σ₁ fuel stim) = obs (run d σ₂ fuel stim)
```

**TRAP.** Two, and both type-check. A bare `∀ σ₁ σ₂, run σ₁ = run σ₂` is
about whatever the trace type happens to be today — coarsen the observation
and more programs become deterministic; expose per-region internals and
designs become non-deterministic *by construction*. And `RaceFree →
determinism` asserted **tier-wide** is vacuous wherever the two are one
predicate, while dropping the `RaceFree` hypothesis to make it prettier makes
the theorem **false**: IEEE 1800 leaves same-region races unspecified on
purpose. Determinism is a PREMISE or a PER-DESIGN theorem, never a tier-wide
conclusion.

**INCIDENT.** The SV false-theorem audit — `docs/backlog.md` *"DETERMINISM IS
OBSERVATION-INDEXED — assumption 5's sibling"*, landed as
`docs/family-architecture.md` §6. Five `_det` theorems must be re-established
through `cycleOf`: *they were never false, they were about a different
trace.* The `RaceFree` half is `docs/proof-framework-research.md` §7.4, the
survey's own "most important sentence in §7".

## 2 — Membership sites

**FORM.** The disjunction lives **inside** an atomic state predicate:
`obs (run …) ∈ permitted site`. Equality is the singleton case, so every
existing site is already correct under the membership rule.

**TRAP.** Spelling a bounded-error site with `⊕`. Outcome conjunction carries
a load-bearing `S ≠ ∅` side condition, which makes `⊕` a **reachability**
claim — it asserts all the listed outcomes are realizable. That converts a
**permission** into an **obligation**, which is strictly stronger and, for
Ada, false. The other direction (`∨` in Outcome Logic: *all* outcomes satisfy
`P` or *all* satisfy `Q`) is wrong too. Byte-equality at such a site
manufactures DIVERGEs against a zero-tolerance invariant.

**INCIDENT.** `docs/proof-framework-research.md` §5.4, verdict **ADOPT-NOW as
a prohibition** — *"not adopting it is the risk; it would silently strengthen
every Ada verdict into a falsehood."* The site class was minted by Ada,
`docs/backlog.md` §L63, and lands in `docs/family-architecture.md` §5.1:
*MATCH is MEMBERSHIP in that set, not equality with one oracle's observable.*

## 3 — ∀-schedule verdicts and counterexample witnesses

**FORM.** Three verdicts, three different quantifier structures:

| verdict | triple | quantifiers |
| --- | --- | --- |
| ∀-schedule MATCH | `⟨⌈P⌉⟩ C ⟨□ Q⟩` (demonic) | `∀σ⊨P. ∀τ ∈ ⟦C⟧(σ). τ⊨Q` |
| DIVERGE-with-witness | `⟨⌈P⌉⟩ C ⟨♢ Q⟩` (angelic) — a **LISBON triple** | `∀σ⊨P. ∃τ ∈ ⟦C⟧(σ). τ⊨Q` |
| Incorrectness Logic — **not ours** | O'Hearn's triple | `∀τ⊨Q. ∃σ⊨P. (σ,τ) ∈ ⟦C⟧` |

Our witness is concrete and executable, not merely asserted: a `#guard` on
the bad schedule's observable.

**TRAP.** Citing **Incorrectness Logic** for DIVERGE-with-witness. It is a
different quantifier structure — *every state in the post is reachable from
some pre-state* — and O'Hearn's motivation (dropping disjuncts to stay in
bounded memory) is a scalability concern that does not apply here. *Getting
this wrong would attach our verdict to the wrong theorem.*

**INCIDENT.** `docs/proof-framework-research.md` §5.3 (name and collapse
argument in §5.7); handed to every verdict emitter in
`docs/backlog/research.md` `2026-08-22-research-1`.

## 4 — Invariants for folds

**FORM.** Layer it. A per-round primitive, the accumulator fact **derived**
from it, and the schedule-level invariant stated over the primitive:

```lean
structure FoldInv gamma value best rs where
  sound  : ...
  rounds : ∀ r ∈ rs, RoundOK gamma value r
  attain : ...
```

`FoldInv` carries the **round** obligation only; each exit's corollary takes
the direction it needs.

**TRAP.** Baking both directions of a boundary into one invariant. The
fail-low arm needs `value ≤ sc`; the fail-high arm needs the exact converse.
Supplying both asserts calmness — a real finding — but it **degenerates the
cut arm**: under both premises a cut forces the stand-pat to have met the
window unaided, which is **3.5% of cuts**, never the **84%** that cut on a
searched move. The joined theorem is true and about almost nothing.

**INCIDENT.** `docs/backlog/sunfish-rtrack.md` `2026-08-22-sunfish-rtrack-4`;
the joined theorem was nearly shipped as a headline before it was caught —
*the vacuity discipline biting at the joint between two lanes' vocabularies.*

## 5 — Fuel placement

**FORM.** Fuel is a **parameter of the statement**, lifted by a monotonicity
lemma, and it does not appear in the surface statement at all. The judgment
layer is the threshold form, with the collapse available:

```lean
(∃ t, ∀ F ≥ t, exec F w = .ok w' v)  ↔  (∃ F, exec F w = .ok w' v)
```

House rules: induction on math variables, never on fuel; typed surface in
statements, no `Val`, no fuel, no AST.

**TRAP.** A fuel **numeral in a hypothesis**. `… 5 …` does not say "some
fuel", it says *five is enough* — and five was not; the genexp needs ten. The
corollary is the whole rule: **numerals are safe in a gate you PROVE (it
fails loudly) and dangerous in a gate you ASSUME (nothing fails at all).**
With symbolic fuel a mismatch is an application type error naming both sides;
with numerals the same off-by-one presents as a multi-minute `whnf` timeout
(see `tools/diagnose.sh`, signature `whnf-timeout`).

**INCIDENT.** `docs/backlog.md` §L24 — the fuel numeral was one of two
independent reasons the same premise was unsatisfiable, and either alone made
the chain **vacuous**; restated as standing law in §L25. The ∃F collapse
(Leroy & Grall Lemma 14) is `docs/proof-framework-research.md` §4.1, verdict
**pilot** — **probe one file first; not yet cashed.**

## 6 — Spec half vs interpreter half

**FORM.** The axis is *"does the STATEMENT mention the interpreter?"* — not
old versus new. A theorem that can be stated about the mathematics **should
be**, and the interpreter-facing statement is the thin layer that connects
it.

**Measured: 949 theorems = 615 mathematics (65%) + 334 interpreter-facing
(35%).** The mathematics recompiles unchanged under a definition swap; the
35% is the entire re-founding scope; four files re-found to nothing at all.

**TRAP.** Writing a spec-side fact into an interpreter-shaped statement
because that is where you needed it. *The 35% is not work you can decide to
have done differently after the fact.* The corollary is the usable half: **a
proof can be interpreter-heavy and still transport untouched if its statement
never mentions the interpreter — the proof's vocabulary is free, the
statement's is not.** And in the other direction: semantic answers transport,
heap-size ledgers transport only if allocation is unchanged, and **fuel
thresholds do not transport at all.**

**INCIDENT.** `docs/backlog.md` *"THE SPEC/INTERPRETER SPLIT HAS A PRICE TAG
— 65% of the estate survives a definition swap"*; landed as
`docs/family-architecture.md` §8 step 9. The decisive part: **the split was
not made for this** — it was made for proof-engineering reasons long before
any rebuild existed, and that choice is worth two thirds of the migration.

## 7 — Output-determined specs

**FORM.** Bind the answer in the **result**, never take it as an input the
caller supplies:

```lean
⦃P⦄ prim args ⦃⇓ r => ⌜lookup ... = some r⌝⦄
```

**TRAP.** Answer-as-input. With the answer as a parameter, mvcgen unified it
against **the loop accumulator** — a wrong-but-typechecking unification that
poisons every downstream VC. Measured twice: 23 VCs with dependent
metavariables became 12, and a second gate's went 3 from a poisoned start,
purely by moving the answer into the result binder.

**INCIDENT.** `docs/mvcgen-pilot.md` §3.3 (the LAWS table, *"specs must be
OUTPUT-DETERMINED"*) and §5.2; recorded in `docs/backlog.md` §L61 as one of
four things worth taking now at zero cost; adopted family-wide in
`docs/c-semantics-design.md` §4.1.

## 8 — Named refusal primitives

**FORM.** Route every refusal through a **named** primitive with its own
`@[spec]` lemma (`refuse` / `liftRes`). And keep the two channels apart: `ρ`
is the **program's** channel (exceptions, abrupt completions, `panic`) — a
language construct can reach it; `Halt` is the **model's** channel (refusal
with a structured payload, and timeout) — **no language construct can ever
reach it, by type.**

**TRAP.** A bare polymorphic `throw` inline. `Std`'s `Spec.throw_Except` at
this pin sits under a `variable` block it does not use, so the monad is
undetermined by the conclusion: four metavariable goals, and the declaration
is **rejected outright** for universe level metavariables. Second trap:
pooling refusal causes — REFUSE has four disjoint causes that retire on
completely different schedules, and pooling them makes the scoreboard
unreadable.

**INCIDENT.** `docs/mvcgen-pilot.md` §1.4 — *"record it as a rule, not a
hack: a refusal is a first-class notion in this family."* The two-channel law
is `docs/backlog.md` *"FAMILY LAW — one `Except`/`throw` pattern, every
tier"*.

## 9 — Frame predicates

**FORM.** One named predicate collecting exactly what the world contributes,
plus a stability lemma per shape a step leaves:

```lean
def PstAt (w : World) : Prop := ...
theorem PstAt.push / .append / .update_ne
```

It converts *"does the value survive this step?"* into *"does `PstAt` survive
this step?"* — **a question about the heap rather than about the
interpreter.**

**TRAP.** Inlining the same world fact into each gate. It is provable, it
works, and it **does not transport**: *an altitude lemma that names what the
world contributes is re-founding-proof, and a gate that inlines the same fact
is not.* Second measured cost: before `PstAt` the residue obligation could
not be stated without unfolding four theorem signatures; after, it is one
line in the consumer's own vocabulary.

**INCIDENT.** `docs/backlog/sunfish-rtrack.md` `2026-08-22-sunfish-rtrack-1`
§1; the transport ruling is Class 2 of `2026-08-22-sunfish-rtrack-3`.

## 10 — Inversion lemmas for threshold-defined judgments

**FORM.** A threshold judgment (`∃ t, ∀ F ≥ t, …`) is a **definition, not an
inductive**, so the constructors build it and the **eliminators are theorems
you state and prove**: an "exhausts" inverse and an "uncons" inverse. Both go
through a **single fuel** — instantiate the threshold once, destructure the
interpreter's own `match`, re-introduce. Hand the intermediate world over
existentially; the per-step worlds are non-uniform anyway (measured: 1 to 25
objects per step).

**TRAP.** Reaching for `cases`. *Because the judgment is `∃ t, ∀ F ≥ t, …`
and not an inductive, that direction is a theorem and not a `cases`, which is
exactly why nobody had it.* Adjacent trap: concluding a raw `∃ w' t, ∀ F ≥ t,
… ∧ …` whose second conjunct **is** the judgment but not in those words — the
inverses cannot fire until it is renamed.

**INCIDENT.** `docs/backlog.md` §L58 — fifteen lines instead of an induction,
because neither side has to agree on a threshold.

## 11 — Well-formedness premises

**FORM.** One named `structure` with projections, plus a predicate on the
**free** variable (`IsPosition pos := ∃ b sc …, pos = posOf …`) rather than
replacing the variable with eight quantifiers — so the consumer reads
character-for-character as before. `#guard` the structure **satisfiable** on
the shipped code.

**TRAP.** Quantifying over something the shipped code constrains and the
statement does not. `BoundRefines` quantified over an arbitrary value; at
`.int 5` the shipped `bound()` REFUSES, so the ∃-conclusion has no witness —
**false at every depth, for every value function**, with a two-slot witness
world satisfying every hypothesis it states. And note the docstring that
*"deliberately does not say"* anything about the clock: **saying nothing is
not neutral** — it admits the node counts at which the code stops.

**INCIDENT.** `docs/backlog.md` §L26, `BoundRefines` **REFUTED**. Downstream,
the theorem the campaign was priced to prove became a one-liner for every
value function: *already true, says nothing, and cannot fail loudly.*

## 12 — Partial correctness

**FORM.** The strengthened form: *every run either times out or returns
exactly this value.* Prove the total judgment and get the partial one free by
corollary.

**TRAP.** Naive partial correctness — *"if it returns `.ok`, the value is
`v`"* — is **vacuously provable for every `v`** whenever the callee raises or
diverges. It is named in the house docs as *a reward-hackable objective for
an AI prover*. The strengthened form is falsifiable: provably inconsistent
with the raising and unsupported judgments.

**INCIDENT.** `AGENTS.md` judgment-vocabulary table and its failure-modes
section; `docs/explanation.md`, *two disciplines keep fuel-based partiality
from degenerating into vacuity* (the other being non-vacuity checks before
any theorem).

## 13 — Short-circuiting constructs

**FORM.** **A short-circuiting construct's out-world is a function of its
ANSWER; the world goes in the hypothesis, not the conclusion.** The
unevaluated operand appears in no hypothesis and in no part of any
conclusion, and the out-memory named is the one the hypothesis introduced for
the operand that actually ran.

**TRAP.** "Evaluate both and combine" — a conclusion mentioning a world the
run may never reach. *A statement of the other shape is unprovable there,
which is the point.* The discriminator: a **full** drain is not
short-circuiting, so its out-world **is** a function of its inputs and may
appear in a conclusion.

**INCIDENT.** `docs/c-semantics-design.md` §4.3 (181 C sites: `&&` 111, `||`
28, `?:` 42, `,` 1), demonstrated rather than asserted in `docs/backlog.md`
§L83 — one term with one uninitialised object answers `0` at one input and
**REFUSES** at another.

## 14 — Gate premises, in the residue's spelling

**FORM.** Conclude with the **computed** heap, not an abstract one, and spell
each premise the way the tactic's residue leaves it (normalised slot lookups,
the literal class NAME, membership facts).

**TRAP.** An abstract-witness conclusion, or a premise in the source's
spelling rather than the residue's. `py_simp` inlines the subscript-store
path past the store helper, and erasing that helper does not stop it — *a
premise about it cannot match what the tactic leaves*, because **simp's erase
does not remove a lemma the tactic itself adds to its list**. One measured
line becomes four premises in the residue's own spelling; without that, the
gate reads as *unprovable* rather than as *mis-spelled*.

**INCIDENT.** `docs/backlog.md` §L20 (*the precedent was there and was
rediscovered rather than read*), re-applied at a new site in §L38, where the
gate then elaborated on the second attempt in 3.8 s against a session priced
for the long route.

## 15 — Existentials

**FORM.** An `∀`-over-fuel-offset premise is the cheap substitute for an
existential judgment whenever the mover and its consumer are inside the same
theorem. **The existential earns its keep exactly when one theorem's
conclusion becomes another's hypothesis.**

**TRAP.** Reaching for the judgment by reading the *shape of the expression*.
Four general lemmas were drafted for the judgment route and **all four were
thrown away**: at symbolic fuel, one `py_simp` crossed them. *What decides is
the shape of the OBLIGATION, not the shape of the expression.*

**INCIDENT.** `docs/backlog.md` §L38.

## 16 — Read-only primitives

**FORM.** Pin the pre-state on both sides — assume `st = st0`, conclude
`… ∧ st = st0`.

**TRAP.** **`Triple` does not frame the state.** An unframed read leaves an
unprovable state equality in the loop's success VC: the read-only-ness you
assumed is simply not in the statement.

**INCIDENT.** `docs/mvcgen-pilot.md` §3.3 — `Std` ships an observation
combinator for exactly this.

## 17 — Definitions the proof layer can state about

**FORM.** Choose the representation so a **lemma** can be written about it,
not merely so a `#guard` passes.

**TRAP.** Trusting the guard. A string-iterating definition passed its
`#guard` — the elaborator unfolds far enough — while **`rfl` and `decide`
both got stuck**, because the iteration goes through `String.Pos`. The law:
**`#guard` is a WEAKER oracle than `rfl`, so a guard passing does not certify
that a lemma can be written.** A primitive the guards can evaluate and the
proof layer cannot state is a **fidelity gap** — so the definition moves,
rather than the claim being weakened.

**INCIDENT.** `docs/backlog.md` §L88 (two definitions moved), the sharper
form of §L82's partial-definition law.

## 18 — Refinement and cross-model agreement

**FORM.** A **function-valued projection**, so the witness obligations
vanish — there is no `∃` to witness:

```lean
theorem cycleOf_runRegion (d : Design) (h : d.isCycleFragment = true)
    (σ : ScheduleOracle) (fuel : Nat) (stim : List SvState) :
    (runRegion d σ fuel stim).map cycleOf = run d σ fuel stim
```

Where the two sides can only be `≤`-related, it is **refinement, and
refinement is ∀∃** — then the determinism side conditions come back. For
stuttering, a simulation relation plus a **measure**.

**TRAP.** Two silent failures. **Forward simulation fails exactly when the
concrete system resolves a nondeterministic choice EARLIER than the abstract
one** — you must pick the abstract witness before the deciding information
exists; forward and backward are each individually incomplete and only their
composition is complete. And **a boundary-only statement is too weak under
mid-cycle observability**: one display statement, PLI callback or testbench
read makes the obligation trace-level rather than state-level, and
retrofitting that is expensive.

**INCIDENT.** `docs/proof-framework-research.md` §7.3 and §6.4 — ADOPT-NOW as
vocabulary and checklist, NOT-FOR-US as a general framework; the theorem
itself is `docs/sv-r1-scheduler.md` §5.3.

## 19 — Refusal causes, told apart by quantifier direction

**FORM.** `∀` over **orders** is the order-dependence refusal: *every*
admissible order gives the same observable. `∃` over **outcomes** is a
membership site: the model's outcome is *some* permitted one.

**TRAP.** Filing a bounded error as order-dependence — *the quantifier is the
other way round* — or as `undefined`, which is **a false statement about the
language, and false in the expensive direction**: the refusal becomes
indistinguishable on the scoreboard from a tier gap. The mirror error is
mapping one language's bounded races onto another's undefined behaviour,
which refuses programs the first language fully describes.

**INCIDENT.** `docs/family-architecture.md` §4.3, minted by
`docs/backlog.md` §L63 — *that ∀/∃ flip is the whole finding.* Note the
prediction that **failed**: a fifth refusal cause was expected at Ada and did
not appear; the gap was one level up, in the scoreboard.

## 20 — Invariant shape and altitude

**FORM.** A top-level **flat `∧`-chain**, so the loop tactic splits it into
named hypotheses. And state the batch at the **composable** primitive, letting
the readable singleton form be the corollary.

**TRAP.** Re-conjoining before `grind`: **e-matching instantiates from atomic
facts, not conjunctions.** And stating every gate over a one-statement list —
the shape a reader wants and the wrong shape for composition, because the
list evaluator peels one statement at a time while chaining needs the
single-statement primitive. With the conversion lemma, the composition became
four rewrites instead of a page of bookkeeping.

**INCIDENT.** `AGENTS.md` failure-modes table; `docs/backlog.md` §L20,
*"the composition's blocker was the gates' own shape"*.

## 21 — Re-proving: never repair a statement to make a proof pass

**FORM.** Published statements are **normative — reproduce them exactly**. A
genuinely needed hypothesis is a **semantics finding**: take it through the
differential harness first. A hypothesis that turns out unneeded is **kept**,
with the fact recorded.

**TRAP.** Adding a hypothesis to close a goal (this narrows the claim
silently — §0.1's forbidden move) or deleting one this toolchain happens not
to need (this loses the record). And the discharge rule: **a premise is not
paid until something DISCHARGES it** — land every gate with the corollary
that consumes it, in the same pass, or the next pass inherits a theorem that
may say nothing. The method that found all three of §L24's defects: *stop
assuming the hypothesis and try to build it.*

**INCIDENT.** `AGENTS.md` failure-modes, *statement discipline when
re-proving*; the discharge law is finding 1 of `docs/backlog.md` §L24 and law
3 of §L25.

---

## 22 — Opening the monad stack: once, where the stack is defined

**FORM.** The stack is unfolded to its concrete representation **exactly
once**, in the module that **defines** it, and every downstream proof works
through the lemmas that opening produced. Not zero times (something has to
connect the abstraction to its representation) and not twice (two openings are
two definitions of the same thing, kept in step by hand).

**TRAP.** The opening migrates outward one proof at a time, because each
individual proof is easier to close by unfolding than by finding the lemma.
Nothing fails — every such proof is correct — and the cost is paid later, when
the stack's representation changes and the repairs are spread across every
module that opened it. **The tell that it is happening is a proof that unfolds
`Functor.map`**: a proof reasoning about the *stack's plumbing* rather than
about the *program*, in a module that has no business knowing the plumbing
exists. Treat that unfold as a signal to go add a lemma where the stack is
defined, not as a step to keep.

**AND THE LAW IS CONDITIONAL ON WHAT THE TIER'S RUN TYPE *IS* — minted by
census, not by analogy (Go, `6a73111`).** "Open the stack once" presumes there
is a stack to open. There is a fork, and the seam's whole shape turns on it:

* **the run type is a DATATYPE** (Python's `Run`): `bind` **reduces by
  cases**, so there is **no opener and none is needed** — Python never wrote
  one. The wall that tier hit was elsewhere: the **approximation-order
  congruences**.
* **the run type is a TRANSFORMER STACK** (Go's `GoM`): nothing reduces by
  cases, so **the opener is exactly what is missing**, and it is **one lemma
  wide**.

> **Ask what the run type IS before pricing the seam. A datatype's cost is its
> CONGRUENCES; a stack's cost is its OPENER.**

**THE GUARD, and it is the transferable half.** The census began from a real
measurement — `Python/Obs.lean` is **158 KB and 79 theorems** — and the honest
report is that **quoting Python's 79 theorems as the price would have been the
wrong read of a real number.** Not a wrong number: a right number **about a
different structure.**

> **A number from another tier measures THEIR structure. It prices yours only
> if the structures match — establish that first, or the census you skipped is
> the one that mattered.**

This is MEAS-1 (*census before pricing*) with the failure mode named: pricing by
**analogy** feels like pricing by **measurement**, because there is a measured
number in it.

**INCIDENT.** The fuelMono lane, staged on ticket 40057 — recorded here
**conditional on that landing** — refined by the Go lane's seam census
(`6a73111`, on master). Related: `docs/family-architecture.md` §3.4's *one
monad, one `vcgen`* — the same rule at the family scale, of which this is the
per-module form — and §3.4's *the ORDER lifts; the CONGRUENCES don't*, which is
why the datatype tier's congruences never became the stack tier's problem.

---

### Two shapes with NO recorded incident, and they are listed as gaps

* **Totality as a distinct statement shape.** It appears only as the total
  judgment subsuming the partial one by monotonicity — no law, no minting
  incident.
* **Decidability in statements.** The decide-ladder in `AGENTS.md` and
  `docs/lean-structures-census.md` §8 is a **tactic and trust** policy, not a
  statement shape. The decidability-adjacent statement law that *is*
  recorded is entry 17.

An entry gets written when an incident mints it. Until then the honest thing
is an empty row, not a plausible rule.
