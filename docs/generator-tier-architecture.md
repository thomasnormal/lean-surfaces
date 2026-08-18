# The generator tier as a VERIFIED object — design memo

Status: **L1, L2 LANDED; L3 LANDED except its walker arm (rules, both
consumer theorems, the effectful bind); L4 COMPLETE (every ray of every
piece — and it REFUTED §4's framing of L4, see below); L5 LANDED as the
FRAME-level flagship** — `gen_moves_yields_ref`
(Examples/python/sunfish/genmoves_scan.lean): the shipped generator, as a
suspended machine over the shipped AST, yields exactly `Ref.refMoves` on an
arbitrary board. `GenMovesEqRef` — the same claim about the heap OBJECT the
call returns — did NOT land, and the reasons are recorded rather than
guessed: the object-level drain needs a locality property of `execGen`
(L2's own recorded remainder), and the statement as frozen is FALSE because
`drain` runs every step at a constant fuel (docs/backlog.md §L5 LANDED
carries the counterexample and the one-line repair, deliberately not
applied). Written
2026-08-16 after the ray leg of the
`gen_moves` theorem stopped on tooling rather than on effort
(docs/backlog.md §the ray leg, factored). It exists so that a "go" starts
landing 1 instead of starting design — and it did: L1 landed 2026-08-16
(the string-as-list bridge, VCTactic.lean §strings as lists of characters;
gate `at?_eq_indexVal`), L2 landed 2026-08-17
(`LeanModels/Python/VCGen.lean` — `GenYields`/`GenYieldsPrefix`/`GenEmits`
and the frame rules; gate `Examples/python/gen_lab/proof.lean`, the first
generator theorems in the repo), and L3's rules landed the same day
(`IterSteps`, `EvalsIn`/`EvalsIn.genCall`, `PyStmtTriple.forGen`; gate
`total_calls` — the first arrow-form spec for a function that consumes a
generator), with its tail following (`PyStmtTriple.assignNameIn`, and
`two_phase_calls` — a generator ABANDONED by one loop and RESUMED by the
next, which is what exercises the lazy half). L3's two OPEN pieces are the
walker automation and §4's `bound_probe` gate, decomposed with their real
prices in docs/backlog.md §L3 LANDED (core) and §L3 TAIL LANDED — the
walker arm has THREE blockers, not the one the first census found, and the
biggest is that the walker's invariant grammar pins a single world. All
landings, their measurements, and their recorded remainders are in
docs/backlog.md §L1 LANDED / §L2 LANDED / §L3 LANDED / §L3 TAIL LANDED /
§L4 PARTIAL.
Everything BELOW is the original design text, unedited — the estimates are
what they were before the work, which is what makes the calibration notes
in the backlog meaningful. THREE of its predictions were revised by contact
with the code and the backlog says how: `EvalsTo.genCall` had to become
`EvalsIn.genCall` (a call that allocates cannot be a pinned-state fact),
the consumer-level `GenYieldsPrefix` turned out unnecessary
(`Inv [] = False` is the break case), and — the biggest —
**§4's L4 is mis-addressed: the ray is a `forGen` frame over a heap
`<count>` OBJECT, not a `countFrom` frame**, because `count(…)` is a call
that allocates its own generator. Measured on the shipped AST, not
recalled; docs/backlog.md §L4 PARTIAL prints the stack. `enumerate(…)`
behaves the same way, so L5's board leg inherits the correction.

Everything below is censused against the tree at `31ff3fb`, not recalled.

---

## 0. The finding that revises the price

The stop-and-report on ray agreement said the blocker was, in part,
"symbolic string/char reasoning" — and priced it as open-ended. **That part
was too pessimistic, and the census says so.** Every string operation
`gen_moves` performs is already defined *through `String.toList`*:

* `strCharVals s = s.toList.map (fun c => .str (String.ofList [c]))`
* `indexVal (.str s) (.int i)` → `normIndex i s.length`, then
  `.str (String.singleton (s.toList.getD n ' '))`
* `strContains s sub = (strFindAux s.toList sub.toList).isSome`

No `String.Pos`, no UTF-8 byte arithmetic anywhere on the path — the hostile
part of Lean's `String` API is simply not on it. And the reference
enumeration was already written over `List Char` (`Ref.at? : List Char → Int
→ Except String Char`), so the two sides meet in the same representation.

What is genuinely missing is that **the Python layer contains zero theorems
about strings at all** (measured: no `theorem` in `LeanModels/Python/*.lean`
mentions `String.toList`, `strCharVals`, `strContains`, or the `.str` arm of
`indexVal`). That is a small, enumerable family to write — not a research
problem. Section 3 prices it.

The rest of the wall stands: there is no specification vocabulary for
generators, and no walker case. Sections 1 and 2 draw those.

---

## 1. The object: what a generator IS here, and what a spec must say

### 1.1 What the interpreter already gives

A suspended generator is a heap object `Obj.generator qname locals cont
status` whose `cont : GenCont = List GenFrame` is a **frame stack**
(`LeanModels/Python/Runtime.lean`). The frame kinds, verbatim from the
census, are the whole surface:

| frame | meaning |
|---|---|
| `block rest` | finish these statements, then the frames below |
| `forSeq target remaining body` | `for` over an immutable value snapshot |
| `forList target a i body` | `for` over a heap list — LIVE cursor at `i` |
| `forGen target a body` | `for` over another generator |
| `whileLoop test body orelse` | re-entering re-tests |
| `enumSeq i remaining` | `enumerate` over a snapshot |
| `enumList i a cur` | `enumerate` over a heap list — live cursor |
| `countFrom cur step` | `itertools.count` — never exhausts |

Two execution functions:

* `execGen m fuel st k : Run FrameState (Option (RVal × GenCont))` — one
  step of the machine: either it yields `(v, k')` or the stack runs out
  (`none`). **Resumable, and the result already carries the resumption.**
* `stepIter m fuel w a : Run World (Option RVal)` — the heap-object wrapper:
  flip `status` to `.running`, `execGen`, write the new `cont` back.
  `drainIter` / `anyAllIter` (H6) sit on top.

Contracts that exist today: `stepIter_mono`, `execGen_mono`,
`execForGen_mono` (Obs.lean) and clock erasure (`CEStepIter` / `CEExecGen`).
That is **all** of it. No triple, no invariant vocabulary, and — measured —
`Examples/python/gen_lab` carries 73 `#py_check`/`#guard` differential rows
and **no `proof.lean` at all**. Generators in this repo have been *run*
exhaustively and *reasoned about* never. The first generator theorem is
still unwritten.

### 1.2 The structural insight the design rests on

`genPlan : Stmt → GenPlan` classifies every statement into
`.delegate` (no `yield` in it) or one of five suspendable shapes
(`.yieldHere`, `.branch`, `.whileHere`, `.forHere`, `.refuse`). The
`.delegate` arm calls **`execStmt`** — the ordinary statement executor.

So the generator tier does **not** re-implement statement reasoning. It is a
five-constructor extension sitting on top of the layer-1/2 triples that
already exist, and every yield-free statement inside a generator body is
discharged by `py_vcgen`'s existing machinery. That is what makes this a
2-week job rather than a re-do of the VC stack.

### 1.3 What a spec must state: `GenYields`

The natural object is not a Hoare triple over a statement list — it is the
**remaining output** of a suspended machine. Proposed, in the repo's
fuel-threshold idiom:

```lean
-- (illustrative — proposed, not in the tree)
/-- From state `st` with frame stack `k`, the generator yields exactly `vs`
and then finishes, landing in `st'`. Total: `timeout` is excluded by the
threshold, `unsupported` by there being no arm for it. -/
def GenYields (m : Module) (st : FrameState) (k : GenCont)
    (vs : List RVal) (st' : FrameState) : Prop :=
  ∃ t, ∀ F ≥ t, drainGen m F st k = .ok st' vs

/-- The lazy half: the first `n` values, with the machine left suspended at
`k'` — what a consumer that BREAKS needs (`bound`'s beta cutoff). -/
def GenYieldsPrefix (m : Module) (st : FrameState) (k : GenCont)
    (vs : List RVal) (st' : FrameState) (k' : GenCont) : Prop :=
  ∃ t, ∀ F ≥ t, stepGenN m F st k vs.length = .ok st' (vs, k')
```

Two definitions rather than one, deliberately: laziness is semantically
load-bearing here (docs/backlog.md §H4 — an unconsumed yield must not run
its TT-writing search), so a consumer that abandons the generator gets the
prefix form and no total obligation. `GenYields` is `GenYieldsPrefix` plus
"and then it finishes".

**Composition is list concatenation**, which is the property that makes the
rules pleasant: a stack `f :: k` yields what `f` yields (with `k` still
below) followed by what `k` yields. One rule per frame kind, and the
`.block` rule splices an existing `PyStmtTriple`:

| rule | shape |
|---|---|
| `yields_nil` | `GenYields m st [] [] st` |
| `yields_block_delegate` | `PyStmtTriple m P s Q` + `GenYields` of the rest ⟹ `GenYields` of `block (s :: ss) :: k` |
| `yields_yieldHere` | `EvalsTo m st e v` ⟹ one output `v`, continuation `block ss :: k` |
| `yields_branch` / `yields_whileHere` / `yields_forHere` | push the frame the interpreter pushes |
| `yields_forSeq` | **the sequence rule**: remainder-indexed invariant, outputs concatenated per element |
| `yields_countFrom` | the ray rule: `countFrom` never exhausts, so the spec is a *prefix* one, ended by the body's `break` |
| `yields_enumSeq` / `forList` / `enumList` / `forGen` | cursor rules (the live-cursor ones carry a heap-stability side condition) |

### 1.4 The invariant a user writes

For `forSeq` — and this is the point — it is **the invariant they already
write for a `for` loop**, plus an output accumulator:

```lean
-- (illustrative — proposed, not in the tree)
(inv := fun (rest : List Int) (best : Int) (out : List RVal) => …)
```

`yields_forSeq`'s proof is `execFor_of_invariant`'s proof with the output
list threaded — structural induction on the remaining elements, no measure
(VC2.lean, landed 2026-08-15). The work is transcription, not discovery.

And the ray: a `countFrom` frame's prefix spec has exactly the
**map-or-constant** shape already proved on the reference side
(`rayBody_map_or_const`, landed 2026-08-16 — every leaf either ignores the
tail or maps one fixed function over it). The two sides of ray agreement are
now the same shape; that is what the ray-leg factoring bought.

---

## 2. The walker case

### 2.1 Where it splices

Mirror the return-position landing (`525c359`). There, layer 2 already had
the primitive (`EvalsTo.call`, whose docstring named `return f(x)` as a
splice point) and layer 3 needed one case that consumed it; the two call
handlers ended up sharing their entire front half (`buildCallEvalsTo`).

The generator analogue:

* **Layer 2 primitive:** `EvalsTo.genCall` — calling a generator function
  evaluates to a `.ref` at a fresh address whose object is
  `Obj.generator qname locals (block body :: []) .created`, with a
  `GenYields` fact derived from the body. This is the missing piece that
  makes a generator *a value with a specification*.
* **Layer 3 case:** `handleForGen`, dispatched from `classify` exactly as
  `handleFor`/`handleRet` are, sharing `buildCallEvalsTo`'s front half when
  the iterable is a call.

### 2.2 What `for x in gen:` discharges — and why it is cheap

The for-loop landing (`fce9c76`) deliberately excluded generators from
`IterVals`, with this note in VC2.lean:

> The `.ref` arm of `for` (H2's live index cursor, `execForList`) and the
> generator arm (`execForGen`) are deliberately NOT here: they are different
> recursion points with a different observational story (mutation during
> iteration), and a rule that quietly covered them would be claiming a
> snapshot semantics the interpreter does not have.

That exclusion was right at the *semantics* level and is not being undone.
But at the *specification* level: **once you hold a `GenYields m st k vs`
fact, the generator is a value list `vs`, and the existing for-rule applies
verbatim.** The remainder-indexed invariant ranges over the not-yet-yielded
values; the structural induction is the one already proved. Laziness only
bites when the consumer breaks early — and that case takes
`GenYieldsPrefix` instead, which is why the spec object has two halves.

So the admission is a sibling of `IterVals`, not a new constructor inside
it (keeping the "snapshot IS the live semantics" invariant of `IterVals`
honest):

```lean
-- (illustrative — proposed, not in the tree)
/-- The iterable is a GENERATOR whose remaining output is `vs`. Not an
`IterVals` constructor: nothing here claims a snapshot, and the fact is a
hypothesis rather than a structural property of the value. -/
theorem PyStmtTriple.forGen {m : Module} {α : Type} (elt : α → RVal)
    (Inv : List α → FrameState → Prop) (a : Addr) (as : List α)
    (hgen : GenYields m st (genContAt st a) (as.map elt) st')
    (hexit : ∀ st, Inv [] st → Q.next st)
    (hstep : …) :                    -- identical to `PyStmtTriple.forLoop`
    PyStmtTriple m (Inv as) (.forStmt target iter body #[] sp) Q
```

Walker-side work: one `classify` arm, one handler, and one extension to
`handleFor`'s element-list reader (today it demands `.listV`; it gains a
`.ref`-to-generator arm that looks for a `GenYields` hypothesis the same way
`findCalleeFact` looks for a `CallsTo` one — including the ∀-quantified
form, which the return-position landing already taught it).

---

## 3. Symbolic string/char: the inventory, and the missing set priced

### 3.1 What `gen_moves` actually asks for

Enumerated from sunfish.py 179–203, every guard on the path:

| guard | primitive | family |
|---|---|---|
| `for i, p in enumerate(self.board)` | `strCharVals` (via `String.toList`) | F1 |
| `p not in "PNBRQK"`, `q in " \nPNBRQK"`, `p in "PNK"`, `q in "pnbrqk"` | `valContains` → `strContains` → `strFindAux` on `toList` | F2 |
| `q = self.board[j]`, `self.board[j + E]` | `indexVal` `.str` arm → `s.toList.getD n` | F1 |
| `p == "P"`, `… == "K"` | `valEq` on `.str` | F3 |
| `d in (N, N + N)`, `d in (N + W, N + E)` | `valContains` on a value tuple of ints | exists (`heapContainsScan`) |
| `directions[p]` | `dictFind` with a str key | exists (dict tier) |
| `abs(j - self.kp) > 1`, `A8 <= j <= H8`, `i < A1 + N` | integer arithmetic | **exists** (`decideArith` simprocs + `captureDischarge`, landed `dbf9719`) |

### 3.2 What exists

* **Mechanism, as prior art:** the captured-run simprocs and discharger I
  landed for the arithmetic guards (`decideArith`, gated by `isIndexGuard`;
  `captureDischarge` = simp's default then `omega`). A char/str family
  plugs into exactly those two hooks — the plumbing question is settled.
* **The list-subscript precedent:** the `arrVal_getElem` family (shared
  since `d19b0e2`) is the same shape one level over: a conditional rewrite
  for an in-range read, side condition discharged from the invariant.
* **String lemmas: none.** Zero theorems in the Python layer.

### 3.3 The missing set

* **F1 — the str-as-list bridge (~6 lemmas).** `s.length = s.toList.length`;
  `indexVal (.str s) (.int j) = .ok (.str (singleton (s.toList[n])))` for
  in-range `j` (the `arrVal_indexVal` twin, negative-index fold included);
  `strCharVals s = s.toList.map (.str ∘ singleton)`; `String.singleton`
  injectivity. All `rfl`-shaped or one-line inductions.
* **F2 — membership (~3 lemmas).** `strContains s (singleton c) =
  s.toList.contains c`, by induction on `strFindAux`. This one lemma is the
  whole family, because `Ref.inStr c lit = lit.toList.contains c` is
  *already the same shape* — the reference and the interpreter agree
  definitionally once it is in hand, with no case split over the literal.
* **F3 — char equality (~2 lemmas).** `valEq` on singleton strs reduces to
  `Char` equality.
* **F4 — a guard simproc: probably NOT needed.** If F1–F3 land, the
  interpreter's guards rewrite into the reference's own vocabulary and match
  syntactically. Budget it as a contingency, not a line item.

**Price: 10–15 lemmas, no new mechanism.** Confidence: high — every one of
them is a statement about `List Char` after one unfolding, and the two
mechanisms they would hang off already exist and are landed.

---

## 4. The landing plan

Five landings, each with its own gate and each collapsing something real —
the py_vcgen arc's template (every landing there turned a hand proof into a
tactic call, which is what kept the arc honest).

### L1 — the string-as-list bridge
**Content:** F1–F3 of §3.3, beside the `arrVal_getElem` family in
VCTactic.lean; wired into `interpLemmas` so captured runs use them.
**Gate:** triad, plus a standalone theorem `Ref.at? b j` = the
interpreter's `board[j]` read at an in-range `j` — the first bridge between
the reference and the model, checkable on its own.
**Unlocks:** nothing alone; prerequisite for L4/L5. Also removes the
`str_lab` gallery's dependence on concrete strings.
**Estimate: 0.5–1 day. Confidence HIGH** (mechanical lemma families have
been my best-calibrated estimates this arc: the `arrVal` promotion and the
builtin-tail fix both landed inside their bands).

### L2 — `GenYields` and the frame rules
**Content:** §1.3 — the two spec objects, `drainGen`/`stepGenN`, the
per-frame rules, and the `drainIter` bridge that connects a heap generator
object to a `GenCont` fact.
**Gate:** triad, plus **the first generator theorem in the repo**: promote
one `gen_lab` differential row (the `aliased` or `two_phase` shape) to a
proved statement. gen_lab has 73 rows and no `proof.lean`; this landing
creates it.
**Unlocks:** the vocabulary; nothing user-facing yet.
**Estimate: 2–4 days. Confidence MEDIUM.** The frame stack is regular and
`genPlan`'s delegate/suspendable split means the yield-free statements come
free — but the live-cursor frames (`forList`, `enumList`) touch the heap and
will want a stability side condition, and that is where the estimate could
stretch.

### L3 — the walker case
**Content:** §2 — `EvalsTo.genCall`, the `classify`/`handleForGen` arm, the
`GenYields`-fact lookup (reusing the ∀-instantiating `findCalleeFact` shape
landed in `525c359`), and `GenYieldsPrefix` for the break case.
**Gate:** triad, plus collapsing `sf_order`'s `bound_probe` — the
moves()-shaped nested generator drained with a beta cutoff — from its
current differential-only status into a `py_vcgen` proof. That exercises
the prefix half, which is the half that can be got wrong.
**Unlocks:** `sf_order`'s ordering theorem (docs/backlog.md §H6 open item
5); the `moves()`-consumed-by-`bound()` capstone stops being blocked on
tooling.
**STATUS (2026-08-17, docs/backlog.md §L8):** the gate's three enumerated
prerequisites are landed (LeanModels/Python/GenBound.lean) and each is
exercised on the shipped program (`Examples/python/sf_order/proof.lean`),
plus a fourth the enumeration had missed. The COLLAPSE is not reached: it
waits on the ordering line's own content (`Position.value` agreement
composed with the `gen_moves` drain), which is this memo's L4/L5, not on
any missing rule.
**Estimate: 1–2 days. Confidence MEDIUM-HIGH** — it mirrors two landings I
just did (the `for` rule and the return-position case), and the reuse is
real rather than hoped-for.

### L4 — ray agreement
**Content:** the `countFrom`-frame prefix spec for one ray, proved equal to
`Ref.ray` using L1's bridge and the already-landed `rayBody_map_or_const` /
`ray_mono`.
**Gate:** triad; the ray lemma stated over an ARBITRARY board.
**Unlocks:** the flagship's hardest leg.
**Estimate: 3–6 days. Confidence LOW-MEDIUM — this is the band that could
double.** It is the first time the machinery meets the real shipped AST
rather than a lab module, and `gen_moves` has six yield sites at three
control-flow depths plus an inlined `yield from`.

### L5 — square agreement, the board scan, and the assembly
**Content:** `directions[p]` for the six keys (kernel-computable, cheap);
the outer `enumerate(self.board)` scan with its `continue` arm; then
`GenMovesEqRef` assembled from L4 + these.
**Gate:** triad; **`theorem gen_moves_eq_ref : GenMovesEqRef`** — the
flagship, said loudly.
**Estimate: 2–4 days. Confidence MEDIUM** given L4 done (the two remaining
legs are structurally simpler than the ray, and the statement is already
written and frozen).

**Total: 9–17 working days.** The ordering constraint is L1 ∥ (L2 → L3) →
L4 → L5; L1 can start the same hour as L2 and by a different hand.

### Stop-conditions, per the standing discipline
Any landing that opens beyond its band gets a recorded decomposition rather
than a heroic push, and no `sorry` reaches master. The two findings this
memo is built on — the `Except`-bind primitive and the unprovable-looking-
right `.error` refutation — both came out of exactly that discipline, and
both are why L4's estimate is a band rather than a number.

---

## COMPLETION NOTE (2026-08-19) — appended, nothing above is edited

The memo's L1–L5 all landed (docs/backlog.md §L2–§L9 for what each cost
against what this memo priced; the 9–17 working days came in at about two).
The whole tier is on `master` as of §L10, and three of this memo's estimates
are worth reading against the outcome:

* **L4 was the band that could double, and did not** — it came in inside the
  band, but for a reason the memo could not have known: the ray is a `forGen`
  frame over a `count` OBJECT, not a `countFrom` frame, so the L1 bridge the
  memo planned to reuse was reused somewhere else entirely.
* **L5's gate said `theorem gen_moves_eq_ref : GenMovesEqRef`, "the flagship,
  said loudly."** It is landed as `gen_moves_eq_ref_of_dirs`
  (`Examples/python/sunfish/genmoves_drain.lean`), with the owner's one-line
  fuel repair to the frozen statement (the statement was FALSE as written —
  a constant drain fuel against an arbitrary board) and two ground
  hypotheses about `initWorld sunfish` that the compiled evaluator confirms
  and the kernel cannot yet afford. The remaining work is a MODULE-INIT
  calculus, which this memo never scoped because it planned around the
  generator, not around the starting world.
* **What the memo got most right** was the ordering constraint. L1 ∥ (L2 → L3)
  → L4 → L5 held exactly, and every landing that opened beyond its band got a
  recorded decomposition instead of a heroic push — §L6's PayloadBlind price
  (quoted at ClockErase scale) was re-measured at a third of it in §L7 because
  the perturbation turned out to be a function.

Two pieces of scope the memo did not have, both now landed: `PayloadBlind`
(§L7 — the interpreter cannot observe a running generator's payload, 18/18
arms) and the `bound_probe` constructs (§L8/§L9). Both were discovered by
building the gate, not by re-reading a plan.

## MODULE-INIT NOTE (2026-08-19) — appended, nothing above is edited

The completion note above ends: *"The remaining work is a MODULE-INIT
calculus, which this memo never scoped because it planned around the
generator, not around the starting world."* That work has now been priced and
partly done (docs/backlog.md §L12 carries every number), and two things about
it are worth recording where the memo's readers will find them.

**The calculus split in two, and only one half was expensive.** Its TOP layer
— the pipeline's own three arms as rewrite rules, general over arbitrary
statements — is `LeanModels/Python/ModuleInit.lean`: eleven theorems, one
rewrite each, 0.4 s to elaborate. That layer alone carried **22 of the
shipped module's 24 top-level statements** into the kernel
(`Examples/python/sunfish/init_chain.lean`), so the flagship now reads
`gen_moves_eq_ref_of_pst` — `GenMovesEqRef` from ONE hypothesis about the
`pst` pipeline (statements 7–8) instead of two about the whole starting
world. Everything else about `initWorld sunfish` — including the address
arithmetic that puts `directions` at slot 63, which is what the flagship
actually needs — is proved.

**The memo's own estimating lesson, one level up.** This memo priced its
landings by the SHAPE of the work and was well calibrated. §L12's route B
was priced by the shape too ("bounded per step, and the literals are large")
and was wrong, because the bound is not the literal size: one Python
statement — `pst[k] = sum((padrow(table[i*8:i*8+8]) for i in range(8)), ())`
— is by itself unreducible in the kernel (420 s / 8.5 GB to an OOM kill from
a fully pinned input state, never finishing), while its two neighbours cost
0.062 s and 1.4 s. A per-statement chain inherits the SOURCE's granularity,
and a source line can hold an arbitrary amount of computation. The next inch
is therefore the sub-statement layer, and its shape is the one this memo
would recognize: the `sum` drain is `drainIter`, so it wants the sibling of
§L8's `EvalsIn.sortedDrain` and then the tier's own `stepIter` machinery —
with the six `pst` iterations proved ONCE, parametrically over the table,
rather than six times over six literals.
