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

end Examples.python.sunfish.monadic_gen
