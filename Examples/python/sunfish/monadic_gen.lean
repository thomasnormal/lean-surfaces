/-
**R2's GENERATOR JUDGMENT LAYER on the monadic interpreter** — the founding.

`fold_depth1.lean`'s chain (§11 of `order_genexp.lean`) closed R2 on the trunk
through `IterSteps` / `IterDrains` / `GenEmits`. Those are class-4 by this lane's
transport taxonomy (backlog entry -3): they name the interpreter, so they are
RE-PROVED here rather than carried across. What transports is their SHAPE, and
the reason it transports is measured — `(kont m (fuel+1)).drainIter a` is
`drainIterAt (kont m fuel) a`, whose recursive call is at `fuel`, so the rebuild
spends ONE fuel level per drained element exactly as the trunk did.

**Two things are different here, and both are improvements.**

*The judgments are SINGLE-WITNESS.* The trunk states them as
`∃ t, ∀ F ≥ t, …` — which is the same workaround as §8's `∀ G` premises and for
the same reason: no monotonicity at the point of use. Here they are `∃ F`, one
witness, with the threshold form RECOVERED as a theorem (`at_fuel`) out of
`Mono.lean`'s generator-family monotonicity. Introduction costs one run instead
of a family; elimination loses nothing.

*They are proved through a NAMED SEAM rather than by unfolding the monad stack.*
See §1. `Mono.lean` is consumed by import throughout and nothing in it is
restated.

**NOT founded by `mvcgen`, and that is a measurement, not a taste.**
`Monadic/Spec.lean` §1.5 records that `mvcgen` splits an inner `match` into one
VC per branch WITHOUT retaining the discriminant equation, leaving unreachable
branches as bare `False`, and that the four-deep gate does not close even with
arm-level `@[spec]` lemmas. `stepIterAt` is built from precisely that shape —
nested matches on `Heap.get?`, then the generator's status, then `Heap.update` —
nested deeper than the gate that already fails. So these are hand proofs with the
discriminants supplied as PREMISES, which is the trunk's method and transports
because the premises ARE the discriminant equations.
-/
import LeanModels.Python.Monadic

namespace Examples.python.sunfish.monadic_gen

open LeanModels LeanModels.Python LeanModels.Python.Monadic

set_option maxRecDepth 8000

/-! ## §1 THE SEAM — now SHARED, and this file's copies are RETIRED

Every proof below reduces a `do` block under `toRun`. This file was founded with
its own `toRun_pure` / `toRun_bind` / `toRun_map`, marked at the time as leaf
copies with an expiry date. That expiry has arrived: the shared versions are on
master in `Monadic/Substrate.lean` §4, stated over the trunk's own `Run.bind`
rather than over a hand-rolled match, and `bind_apply` moved there beside them
under the same fully-qualified name. The copies are DELETED here — §9.2's
consolidation by touch, performed rather than merely scheduled.

They cost nothing to give up and the shared statement is better: `Run.bind` is
the vocabulary every `Run`-level theorem in the trunk already speaks, so the
seam now joins the existing lemma stock instead of sitting beside it. Nothing in
this file needs an import change, because the shared lemmas live in
`LeanModels.Python.Monadic`, which is already open here.

**What the swap cost, recorded because it was PREDICTED and then MEASURED.**
Against the old match-shaped RHS, a bare `dsimp only` reduced the intermediate
`match Run.ok … with …` by iota. Against `Run.bind` it does not: `Run.bind` is an
`@[inline]` def, not `@[reducible]`, so it must be NAMED. Exactly one proof in
this file cared — `genSilent_branch`, which now says `dsimp only [Run.bind]` and
closes with `rfl` for the final bind the second rewrite leaves behind.
`drain_nil` and `drain_cons` were unaffected, because a full `simp` unfolds
`Run.bind` unaided. That difference — full `simp` copes, `dsimp only` must be
told — is the whole of the repoint, and it was verified in a scratch file
against the new RHS before this edit was made. -/
/-! ## §2 THE GENERATOR FAMILY'S MONOTONICITY, consumed

`KontLe` is a fourteen-component conjunction; `stepIter` is its tenth and
`drainIter` its thirteenth. `kontMono` turns `f ≤ f'` into a `KontLe`. Nothing
here is proved — these two name the components this file consumes, so that the
projection is written once instead of at every use site. -/

theorem kont_stepIter_mono (m : Module) {f f' : Nat} (hf : f ≤ f') (a : Addr) :
    (kont m f).stepIter a ⊑ₚ (kont m f').stepIter a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hstep, _, _, _, _⟩ := kontMono m f f' hf
  exact hstep a

theorem kont_drainIter_mono (m : Module) {f f' : Nat} (hf : f ≤ f') (a : Addr) :
    (kont m f).drainIter a ⊑ₚ (kont m f').drainIter a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdrain, _⟩ := kontMono m f f' hf
  exact hdrain a

/-! ## §3 THE PRIMITIVES -/

/-- **One decided step of the generator object at `a`** — the rebuild's
`IterSteps`. One witness, not a threshold. -/
def IterStepsM (m : Module) (w : World) (a : Addr) (r : Option RVal)
    (w' : World) : Prop :=
  ∃ F, toRun ((kont m F).stepIter a) w = .ok w' r

/-- **A whole drain**, likewise. -/
def IterDrainsM (m : Module) (w : World) (a : Addr) (vs : List RVal)
    (w' : World) : Prop :=
  ∃ F, toRun ((kont m F).drainIter a) w = .ok w' vs

/-- **The threshold form is RECOVERED, not abandoned** — the `hop_forall`
pattern of `monadic_fold.lean` §3, applied to a judgment rather than a call. A
single witness gives the answer at every larger fuel, so nothing the trunk's
`∃ t, ∀ F ≥ t` could discharge is lost. -/
theorem IterStepsM.at_fuel {m : Module} {w w' : World} {a : Addr}
    {r : Option RVal} (h : IterStepsM m w a r w') :
    ∃ F₀, ∀ F, F₀ ≤ F → toRun ((kont m F).stepIter a) w = .ok w' r := by
  obtain ⟨F₀, hF⟩ := h
  refine ⟨F₀, fun F hle => ?_⟩
  have hne : toRun ((kont m F₀).stepIter a) w ≠ .timeout := by simp [hF]
  rw [← Run.le_eq (toRun_le (kont_stepIter_mono m hle a) w) hne]
  exact hF

/-- The same for the drain. -/
theorem IterDrainsM.at_fuel {m : Module} {w w' : World} {a : Addr}
    {vs : List RVal} (h : IterDrainsM m w a vs w') :
    ∃ F₀, ∀ F, F₀ ≤ F → toRun ((kont m F).drainIter a) w = .ok w' vs := by
  obtain ⟨F₀, hF⟩ := h
  refine ⟨F₀, fun F hle => ?_⟩
  have hne : toRun ((kont m F₀).drainIter a) w ≠ .timeout := by simp [hF]
  rw [← Run.le_eq (toRun_le (kont_drainIter_mono m hle a) w) hne]
  exact hF

/-! ## §4 THE DRAIN'S INTRODUCTION RULES

The two arms of `drainIterAt`, each at the fuel the rebuild actually spends: the
drain at `F + 1` is one step at `F` followed by the rest of the drain at `F`.
That is the one-level-per-element accounting, now proved rather than observed. -/

/-- **Exhaustion introduces the empty drain.** -/
theorem drain_nil {m : Module} {w w' : World} {a : Addr} {F : Nat}
    (h : toRun ((kont m F).stepIter a) w = .ok w' Option.none) :
    toRun ((kont m (F + 1)).drainIter a) w = .ok w' [] := by
  simp only [kont, drainIterAt]
  simp [toRun_bind, h, toRun_pure]

/-- **And a yield conses**, threading the world through the step and then the
tail. -/
theorem drain_cons {m : Module} {w w₁ w' : World} {a : Addr} {v : RVal}
    {vs : List RVal} {F : Nat}
    (hstep : toRun ((kont m F).stepIter a) w = .ok w₁ (some v))
    (hrest : toRun ((kont m F).drainIter a) w₁ = .ok w' vs) :
    toRun ((kont m (F + 1)).drainIter a) w = .ok w' (v :: vs) := by
  simp only [kont, drainIterAt]
  simp [toRun_bind, hstep, toRun_map, hrest]

/-- The judgment-level corollary: the two primitives compose into a drain
without the caller ever naming a fuel. -/
theorem IterDrainsM.cons {m : Module} {w w₁ w' : World} {a : Addr} {v : RVal}
    {vs : List RVal} (hstep : IterStepsM m w a (some v) w₁)
    (hrest : IterDrainsM m w₁ a vs w') :
    IterDrainsM m w a (v :: vs) w' := by
  obtain ⟨F₁, h₁⟩ := hstep.at_fuel
  obtain ⟨F₂, h₂⟩ := hrest.at_fuel
  exact ⟨max F₁ F₂ + 1, drain_cons (h₁ _ (by omega)) (h₂ _ (by omega))⟩

/-- …and exhaustion closes one. -/
theorem IterDrainsM.nil {m : Module} {w w' : World} {a : Addr}
    (h : IterStepsM m w a Option.none w') : IterDrainsM m w a [] w' := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F + 1, drain_nil hF⟩

/-! ## §5 `GenSilent` — and the trunk's threshold turns out to be an ARTIFACT

The trunk states silent transitions as `∃ d t, ∀ F ≥ t, execGen m (F + d) st k =
execGen m F st₁ k₁`. The `t` is not intrinsic to silent transitions: it is an
artifact of the trunk's FUELED expression evaluator. On the rebuild
`evalOpen`/`execOpen` are fuel-free (structural on syntax), so the only fuel a
continuation step spends is the `K.execGen` recursion itself — exactly one level.
The accounting is therefore EXACT, and the threshold disappears: `d` fuel
performs the rearrangement, `F` runs the residue, and both sides bottom out
together at `F = 0`.

So the definition below quantifies over ALL `F`, from zero, with no `t`. -/

/-- A silent transition: `⟨st, k⟩` resumes exactly as `⟨st₁, k₁⟩` does, `d` fuel
later. No threshold — see the section note. -/
def GenSilentM (m : Module) (st st₁ : FrameState) (k k₁ : GenCont) : Prop :=
  ∃ d, ∀ F, toRun ((kont m (F + d)).execGen k) st
           = toRun ((kont m F).execGen k₁) st₁

/-- **Popping an exhausted block**, the canonical silent step — exact at every
fuel from zero, and the evidence for the section note. -/
theorem genSilent_block_nil (m : Module) (st : FrameState) (k' : GenCont) :
    GenSilentM m st st (.block [] :: k') k' :=
  ⟨1, fun F => by simp only [kont, execGenAt]⟩

/-- **A `while` header is pure frame rearrangement** — also exact. The
`hasYield` premise is what `genPlan` actually tests: a yield-free `while`
DELEGATES instead, which is a different arm entirely. -/
theorem genSilent_while (m : Module) (st : FrameState) (test : Expr)
    (body orelse : Array Stmt) (ss : List Stmt) (k' : GenCont) (sp : Span)
    (hy : (Stmt.whileLoop test body orelse sp).hasYield = true) :
    GenSilentM m st st (.block (Stmt.whileLoop test body orelse sp :: ss) :: k')
      (.whileLoop test body.toList orelse.toList :: .block ss :: k') :=
  ⟨1, fun F => by simp only [kont, execGenAt, genPlan, hy]; rfl⟩

/-- **The branch arm is where the story changes**, and the difference is worth
stating precisely. It EVALUATES the test, and `evalOpen` takes the `Kont`
because an expression may CALL — so this arm is not unconditionally fuel-exact
the way the rearrangement arms are. What survives is better than the trunk's
blanket threshold: the fuel dependence is ISOLATED into one premise about the
test, and the transition is exact relative to it. For a call-free test that
premise holds uniformly in `F` and the arm is exact too.

The premise is spelled as `genPlan`'s RESULT rather than as `hasYield`, because
that is the spelling the path leaves: rewriting inside `genPlan` leaves an
`if (!true) = true` the rewriter then has to be talked out of. -/
theorem genSilent_branch (m : Module) (st st' st₁ : FrameState) (test : Expr)
    (body orelse : Array Stmt) (ss : List Stmt) (k' : GenCont) (sp : Span)
    (v : RVal) (b : Bool)
    (hplan : genPlan (Stmt.ifStmt test body orelse sp)
      = .branch test body.toList orelse.toList)
    (hev : ∀ F, toRun (evalOpen (kont m F) m test) st = .ok st' v)
    (htr : toRun (truthyM v) st' = .ok st₁ b) :
    GenSilentM m st st₁ (.block (Stmt.ifStmt test body orelse sp :: ss) :: k')
      ((if b then GenFrame.block body.toList else GenFrame.block orelse.toList)
        :: .block ss :: k') :=
  ⟨1, fun F => by
    simp only [kont, execGenAt, hplan]
    rw [toRun_bind, hev F]
    dsimp only [Run.bind]
    rw [toRun_bind, htr]
    rfl⟩

#print axioms IterStepsM.at_fuel
#print axioms IterDrainsM.at_fuel
#print axioms drain_nil
#print axioms drain_cons
#print axioms IterDrainsM.cons
#print axioms IterDrainsM.nil
#print axioms genSilent_block_nil
#print axioms genSilent_while
#print axioms genSilent_branch

/-! ## §6 `GenEmits` — and the drain is a RELATION, not a function

The trunk states "what a continuation yields" through `drainGen`, a function it
had to write. That function lives in `VCGen.lean`, not `Semantics.lean`: it is
PROOF-LAYER scaffolding, not an interpreter primitive. The rebuild therefore owes
no such function, and this file does not write one — `GenYieldsM` is an
inductive RELATION whose two constructors are the two things a continuation can
do, each carrying its own single-fuel witness. The relation IS the drain.

That is a definition REMOVED rather than ported, and it pays twice: there is no
`drainGen_mono` to prove, and no fuel-indexed threshold to thread, because each
step's witness is transported by `Mono.lean` where it is needed. -/

/-- **What a continuation yields.** `done` is exhaustion; `yield` is one value
and a resumption. Each step carries its own `∃ F`. -/
inductive GenYieldsM (m : Module) :
    FrameState → GenCont → List RVal → FrameState → Prop
  | done {st st' k} (h : ∃ F, toRun ((kont m F).execGen k) st = .ok st' Option.none) :
      GenYieldsM m st k [] st'
  | yield {st st₁ st' k k' v vs}
      (h : ∃ F, toRun ((kont m F).execGen k) st = .ok st₁ (some (v, k')))
      (hrest : GenYieldsM m st₁ k' vs st') :
      GenYieldsM m st k (v :: vs) st'

/-- **The compositional object**: the frame PREFIX emits `ws` and falls through,
leaving the machine at `st₁` with whatever was below it — for EVERY continuation.
The interpreter only scrutinises head frames, so this is exactly as strong as the
per-frame behaviour, and composition is `List.append` on both sides. -/
def GenEmitsM (m : Module) (st : FrameState) (pre : GenCont)
    (ws : List RVal) (st₁ : FrameState) : Prop :=
  ∀ k vs st', GenYieldsM m st₁ k vs st' → GenYieldsM m st (pre ++ k) (ws ++ vs) st'

theorem GenEmitsM.trans {m : Module} {st st₁ st₂ : FrameState}
    {pre pre' : GenCont} {ws ws' : List RVal}
    (h : GenEmitsM m st pre ws st₁) (h' : GenEmitsM m st₁ pre' ws' st₂) :
    GenEmitsM m st (pre ++ pre') (ws ++ ws') st₂ := by
  intro k vs st' hk
  have := h' k vs st' hk
  have := h (pre' ++ k) (ws' ++ vs) st' this
  simpa [List.append_assoc] using this

theorem GenEmitsM.nil {m : Module} {st : FrameState} :
    GenEmitsM m st [] [] st := by
  intro k vs st' hk; simpa using hk

/-- **A silent transition transfers yields.** Only the HEAD step is rewritten —
the rest of the derivation carries over untouched, which is the whole reason the
relational form is cheaper than a drain function here. -/
theorem GenYieldsM.of_silent {m : Module} {st st₁ : FrameState} {k k₁ : GenCont}
    {vs : List RVal} {st' : FrameState}
    (hs : GenSilentM m st st₁ k k₁) (h : GenYieldsM m st₁ k₁ vs st') :
    GenYieldsM m st k vs st' := by
  obtain ⟨d, hd⟩ := hs
  cases h with
  | done hF =>
      obtain ⟨F, hFe⟩ := hF
      exact .done ⟨F + d, by rw [hd F]; exact hFe⟩
  | yield hF hrest =>
      obtain ⟨F, hFe⟩ := hF
      exact .yield ⟨F + d, by rw [hd F]; exact hFe⟩ hrest

/-- A silent PREFIX, for every continuation, is emission-preserving. -/
theorem GenEmitsM.silent {m : Module} {st st₁ st₂ : FrameState}
    {pre pre₁ : GenCont} {ws : List RVal}
    (hs : ∀ k, GenSilentM m st st₁ (pre ++ k) (pre₁ ++ k))
    (h : GenEmitsM m st₁ pre₁ ws st₂) : GenEmitsM m st pre ws st₂ :=
  fun k vs st' hk => GenYieldsM.of_silent (hs k) (h k vs st' hk)

/-- The `forGen` frame on a YIELD: the inner object steps, the target binds, and
the loop frame is pushed back under the body. -/
theorem genSilent_forGenCons (m : Module) (target : Expr) (ad : Addr)
    (body : List Stmt) (st st₁ st₂ : FrameState) (v : RVal) (k' : GenCont)
    (hstep : ∀ F, toRun (inFrame ((kont m F).stepIter ad)) st = .ok st₁ (some v))
    (hasg : toRun (assignM target v) st₁ = .ok st₂ ()) :
    GenSilentM m st st₂ (.forGen target ad body :: k')
      (.block body :: .forGen target ad body :: k') :=
  ⟨1, fun F => by
    simp only [kont, execGenAt]
    rw [toRun_bind, hstep F]
    dsimp only [Run.bind]
    rw [toRun_bind, hasg]
    rfl⟩

/-- …and on EXHAUSTION: the loop frame pops and the tail resumes. -/
theorem genSilent_forGenDone (m : Module) (target : Expr) (ad : Addr)
    (body : List Stmt) (st st₁ : FrameState) (k' : GenCont)
    (hstep : ∀ F, toRun (inFrame ((kont m F).stepIter ad)) st
      = .ok st₁ Option.none) :
    GenSilentM m st st₁ (.forGen target ad body :: k') k' :=
  ⟨1, fun F => by
    simp only [kont, execGenAt]
    rw [toRun_bind, hstep F]
    rfl⟩

/-- **ONE ROUND of `for x in <generator>` whose body FALLS THROUGH**, at
`GenEmits` altitude — R2's chain step on the rebuilt interpreter. The inner
object yields, the target binds it, the body emits `ws`, and the loop frame is
still there for the rest.

As on the trunk, the loop is NOT packaged as one induction here: an infinite
inner generator has no remainder list to induct on, so the rounds are chained by
the CALLER and `hrest` is where its own induction (or its `break`) goes. -/
theorem GenEmitsM.forGenRound {m : Module} {target : Expr} {ad : Addr}
    {body : List Stmt} {st st₁ st₂ st₃ st₄ : FrameState} {v : RVal}
    {ws ws' : List RVal}
    (hstep : ∀ F, toRun (inFrame ((kont m F).stepIter ad)) st = .ok st₁ (some v))
    (hasg : toRun (assignM target v) st₁ = .ok st₂ ())
    (hbody : GenEmitsM m st₂ [.block body] ws st₃)
    (hrest : GenEmitsM m st₃ [.forGen target ad body] ws' st₄) :
    GenEmitsM m st [.forGen target ad body] (ws ++ ws') st₄ :=
  GenEmitsM.silent
    (pre := [GenFrame.forGen target ad body])
    (pre₁ := [GenFrame.block body, GenFrame.forGen target ad body])
    (fun k => by
      simpa using genSilent_forGenCons m target ad body st st₁ st₂ v k hstep hasg)
    (GenEmitsM.trans hbody hrest)

#print axioms GenYieldsM
#print axioms GenEmitsM.trans
#print axioms GenEmitsM.nil
#print axioms GenYieldsM.of_silent
#print axioms GenEmitsM.silent
#print axioms genSilent_forGenCons
#print axioms genSilent_forGenDone
#print axioms GenEmitsM.forGenRound

/-! ## §7 THE CHAIN — `forGenRound` iterated, and the induction is the CALLER'S

`forGenRound` deliberately does not close the loop: an infinite inner generator
has no remainder list to induct on. What closes it is a FINITE run, and supplying
that finiteness is the caller's obligation. `ForGenRunM` is exactly that
obligation made into an object — some number of rounds that keep, then an
exhaustion — and `forGenChain` discharges the induction over it once, so no
caller writes this induction again. -/

/-- A whole `for x in <generator>` run as the caller sees it. Finite by
construction. -/
inductive ForGenRunM (m : Module) (target : Expr) (ad : Addr) (body : List Stmt) :
    FrameState → List RVal → FrameState → Prop
  | done {st st₁}
      (hstep : ∀ F, toRun (inFrame ((kont m F).stepIter ad)) st = .ok st₁ Option.none) :
      ForGenRunM m target ad body st [] st₁
  | keep {st st₁ st₂ st₃ st₄ v ws ws'}
      (hstep : ∀ F, toRun (inFrame ((kont m F).stepIter ad)) st = .ok st₁ (some v))
      (hasg : toRun (assignM target v) st₁ = .ok st₂ ())
      (hbody : GenEmitsM m st₂ [.block body] ws st₃)
      (hrest : ForGenRunM m target ad body st₃ ws' st₄) :
      ForGenRunM m target ad body st (ws ++ ws') st₄

/-- **THE CHAIN.** The rounds compose into one `GenEmits` for the whole loop. -/
theorem forGenChain {m : Module} {target : Expr} {ad : Addr} {body : List Stmt}
    {st st' : FrameState} {ws : List RVal}
    (h : ForGenRunM m target ad body st ws st') :
    GenEmitsM m st [.forGen target ad body] ws st' := by
  induction h with
  | done hstep =>
      exact GenEmitsM.silent
        (pre := [GenFrame.forGen target ad body]) (pre₁ := [])
        (fun k => by simpa using genSilent_forGenDone m target ad body _ _ k hstep)
        GenEmitsM.nil
  | keep hstep hasg hbody _ ih =>
      exact GenEmitsM.forGenRound hstep hasg hbody ih

/-! ## §8 `bound()`'s OWN fold — a DIFFERENT function, and the distinction matters

Everything above concerns `execGenAt`'s `.forGen` FRAME: the ordering line, where
a generator iterates another generator. `bound()`'s own loop —
`for val, move in moves():` — is not that. `bound()` is not itself a generator,
so its loop runs through `forGenAt`, the `execOpen` path, which returns an
`RFlow` rather than a yield.

The recipe is the same and the function is not, which is worth stating plainly:
a lane that proved the frame arm and assumed the loop arm came with it would have
a gap exactly where the fold lives. These two laws are the fold's interpreter
half at its lowest altitude — one round, and exhaustion. -/

/-- **ONE ROUND of `bound()`'s fold**: the generator yields, the target binds, the
body falls through with `.next`, and the loop continues one fuel level down. -/
theorem forGen_step (m : Module) (target : Expr) (ad : Addr) (body : List Stmt)
    (st st₁ st₂ st₃ : FrameState) (v : RVal) (F : Nat)
    (hstep : toRun (inFrame ((kont m F).stepIter ad)) st = .ok st₁ (some v))
    (hasg : toRun (assignM target v) st₁ = .ok st₂ ())
    (hbody : toRun (execOpenList (kont m F) m body) st₂ = .ok st₃ .next) :
    toRun ((kont m (F + 1)).forGen target ad body) st
      = toRun ((kont m F).forGen target ad body) st₃ := by
  simp only [kont, forGenAt]
  rw [toRun_bind, hstep]
  dsimp only [Run.bind]
  rw [toRun_bind, hasg]
  dsimp only [Run.bind]
  rw [toRun_bind, hbody]
  rfl

/-- …and EXHAUSTION: the loop falls through with `.next`. -/
theorem forGen_done (m : Module) (target : Expr) (ad : Addr) (body : List Stmt)
    (st st₁ : FrameState) (F : Nat)
    (hstep : toRun (inFrame ((kont m F).stepIter ad)) st = .ok st₁ Option.none) :
    toRun ((kont m (F + 1)).forGen target ad body) st = .ok st₁ .next := by
  simp only [kont, forGenAt]
  rw [toRun_bind, hstep]
  dsimp only [Run.bind]
  exact toRun_pure _ _

#print axioms ForGenRunM
#print axioms forGenChain
#print axioms forGen_step
#print axioms forGen_done

/-! ## §9 ARM LEMMAS, GENERAL IN THE STATEMENT — rung 6's actual unit of work

§5's `genSilent_branch` hard-codes `Stmt.ifStmt`. That was the right shape for
proving the ARM exists and the wrong shape for USING it: a real statement slice
(`sbNull`, `sbStand`, …) presents as an opaque `Stmt` with a computed `genPlan`,
not as a literal constructor application. The trunk's own branch lemma takes `s`
plus a `genPlan` premise for exactly this reason, and re-founding copied the
proof rather than the interface.

**This is rung 6's unit of work, and it is smaller than the rung's headline
number suggests.** The ~57 interpreter-facing statements of `bound()` are not 57
independent proofs: they are 57 INSTANTIATIONS of a handful of arm lemmas, each
supplying a `genPlan` equation (by `rfl` on a slice) and the sub-runs its own
statement makes. The arms are shared; only the premises are per-statement. -/

/-- **The branch arm, general in the statement.** -/
theorem genSilent_branch' (m : Module) (st st' st₁ : FrameState) (s : Stmt)
    (test : Expr) (body orelse ss : List Stmt) (k' : GenCont)
    (v : RVal) (b : Bool)
    (hplan : genPlan s = .branch test body orelse)
    (hev : ∀ F, toRun (evalOpen (kont m F) m test) st = .ok st' v)
    (htr : toRun (truthyM v) st' = .ok st₁ b) :
    GenSilentM m st st₁ (.block (s :: ss) :: k')
      ((if b then GenFrame.block body else GenFrame.block orelse)
        :: .block ss :: k') :=
  ⟨1, fun F => by
    simp only [kont, execGenAt, hplan]
    rw [toRun_bind, hev F]
    dsimp only [Run.bind]
    rw [toRun_bind, htr]
    rfl⟩

/-- **The DELEGATE arm** — a yield-free statement runs through the ordinary
executor and the walker moves on. This is the arm every non-control statement of
a generator body takes, so for rung 6 it is the highest-frequency one: most of
`moves()` is assignments and calls, not control flow. -/
theorem genSilent_delegateNext (m : Module) (st st₁ : FrameState) (s : Stmt)
    (ss : List Stmt) (k' : GenCont)
    (hplan : genPlan s = .delegate)
    (hrun : ∀ F, toRun (execOpen (kont m F) m s) st = .ok st₁ .next) :
    GenSilentM m st st₁ (.block (s :: ss) :: k') (.block ss :: k') :=
  ⟨1, fun F => by
    simp only [kont, execGenAt, hplan]
    rw [toRun_bind, hrun F]
    rfl⟩

#print axioms genSilent_branch'
#print axioms genSilent_delegateNext

end Examples.python.sunfish.monadic_gen
