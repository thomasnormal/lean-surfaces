/-
**FUEL MONOTONICITY FOR THE MONADIC REBUILD** — `Monadic.fuelMono`, the one
lemma `docs/backlog/pyrebuild.md` §Owed names, and the ∃F collapse's missing
half. `exf_collapse_abstract` already proves, axiom-free, that a threshold form
`∃ t, ∀ F ≥ t, P F` collapses to `∃ F, P F` for upward-closed `P`; this file is
what makes the interpreter's `P` upward-closed.

**THE DECOMPOSITION, and it is the shape of the rebuild rather than an
accident.** The rebuild splits the interpreter in two — a FUEL-FREE half
(`evalOpen`/`execOpen`, structural on syntax) and a FUELED knot (`kont`,
structural on fuel) joined by the `Kont` record. Monotonicity splits the same
way and the two halves are proved by DIFFERENT inductions:

| half | statement | induction |
|---|---|---|
| fuel-free | `KontLe K K' → evalOpen K m e ⊑ₚ evalOpen K' m e` | on SYNTAX (`evalOpen.mutual_induct`) |
| fueled | `f ≤ f' → KontLe (kont m f) (kont m f')` | on FUEL (`kontMono`) |
| composed | `f ≤ f' → callInMono m f … ⊑ʳ callInMono m f' …` | neither — one application |

The house rule "induction on math variables, never on fuel" is unbroken: the
ONE fuel induction is `kontMono`, and it is framework code, exactly like the
trunk's `Obs.lean` `fuelMono`.

**WHAT IS IMPORTED RATHER THAN REPROVED.** `LeanModels/Python/Obs.lean` already
carries the trunk's `Res`-level monotonicity for the SHARED pure workers —
`heapEqMono`, `valContains_mono`, `setDedup_mono`, `evalCompareOpH_mono`. The
rebuild reuses the maximal trunk (`Monadic/Substrate.lean` §"WHAT IS SHARED"),
so it reuses those proofs too; `Obs.lean` imports only `Python.Logic` and knows
nothing of `Monadic`, so this import creates no cycle. Nothing in `Obs.lean` is
restated here.

**THE CONGRUENCE SET HAS SIX SHAPES: monad (3) + state-zoom seam (2) +
PURE-WORKER seam (1).** `bind`, `ite`, `tryCatch` are the monad's own;
`zoomIn`, `zoomOut` are Core's state-zoom adapters (`Core/Outcome.lean`), which
every tier instantiating `SemMWith` inherits — `inFrame`/`inWorld` are Python's
instances at two lines each. The SIXTH is `PyLe.liftRes`, and it is the seam
where a `Res`-level fact about a fuel-taking TRUNK worker becomes a `⊑ₚ` fact
about the rebuild: `liftRes` is the single door the maximal trunk comes through,
so it is also the only place the `K.fuel` BOUND is consumed. A hole in the SET
is not a missing arm — it shows up as a goal no amount of arm-work can close.

**`PyLe` IS NOT DEFINED THROUGH `toRun`, deliberately.** `toRun` erases the
`RefusalCause` and the diagnostic snapshot (`Substrate.lean`'s
`ofRun_toRun_normalises` states the loss as a theorem), so an order mediated by
it would equate refusals with DIFFERENT causes. That is a weakening of the
relation, i.e. exactly the thing this file may not do to make a proof pass. The
`Run`-level corollary `fuelMono` is derived from the strong order by
`toRun_le`, never the other way round.

Zero `sorry`. Zero `native_decide`. Every theorem's axiom line taken from
`tools/check.sh --axioms`'s verdict, per §5.4a.
-/
import LeanModels.Python.Monadic.Eval
import LeanModels.Python.Obs

open LeanModels LeanModels.Python LeanModels.Python.Monadic

namespace LeanModels.Python.Monadic

/-! ## §0 THE APPROXIMATION ORDER on the monadic tier -/

def PyLe {σ α : Type} (x y : PyM σ α) : Prop :=
  ∀ s, x s = .error .timeout ∨ x s = y s
scoped infix:50 " ⊑ₚ " => PyLe

theorem PyLe_iff {σ α : Type} {x y : PyM σ α} :
    x ⊑ₚ y ↔ ∀ s, x s = .error .timeout ∨ x s = y s := Iff.rfl
attribute [irreducible] PyLe

theorem PyLe.refl' {σ α : Type} (x : PyM σ α) : x ⊑ₚ x :=
  PyLe_iff.mpr fun _ => Or.inr rfl

/-- `PyLe` IS Core's flat order, pointwise — the third in-tree instance after
`Sv.Res.le` and `Python.Res.le` (`Obs.lean`'s `Res.le_iff_flatLe`). Stated as
an iff rather than a definition so `PyLe`'s own spelling, and its ~20
consumers, stay put. -/
theorem PyLe_iff_flatLe {σ α : Type} {x y : PyM σ α} :
    x ⊑ₚ y ↔ ∀ s, FlatLe (.error .timeout) (x s) (y s) := PyLe_iff

theorem bind_apply {σ α β : Type} (x : PyM σ α) (f : α → PyM σ β) (s : σ) :
    (x >>= f) s = (match x s with
      | .error l => .error l
      | .ok (.error e, s') => .ok (.error e, s')
      | .ok (.ok a, s') => f a s') := by
  cases h : x s with
  | error l => simp [Bind.bind, ExceptT.bind, ExceptT.mk, StateT.bind, h, Except.bind]
  | ok p =>
      obtain ⟨r, s'⟩ := p
      cases r with
      | error e =>
          simp only [Bind.bind, ExceptT.bind, ExceptT.mk, StateT.bind, h, Except.bind,
                     ExceptT.bindCont]
          rfl
      | ok a =>
          simp [Bind.bind, ExceptT.bind, ExceptT.mk, StateT.bind, h, Except.bind,
                ExceptT.bindCont]

theorem PyLe.bind {σ α β : Type} {x x' : PyM σ α} {f f' : α → PyM σ β}
    (hx : x ⊑ₚ x') (hf : ∀ a, f a ⊑ₚ f' a) : (x >>= f) ⊑ₚ (x' >>= f') := by
  rw [PyLe_iff]
  intro s
  rw [bind_apply, bind_apply]
  rcases PyLe_iff.mp hx s with h | h
  · rw [h]; left; rfl
  · rw [h]
    rcases hx' : x' s with l | ⟨r, s'⟩
    · right; rfl
    · cases r with
      | error e => right; rfl
      | ok a => exact PyLe_iff.mp (hf a) s'

theorem PyLe.ite {σ α : Type} {c : Prop} [Decidable c] {x x' y y' : PyM σ α}
    (hx : x ⊑ₚ x') (hy : y ⊑ₚ y') :
    (if c then x else y) ⊑ₚ (if c then x' else y') := by
  by_cases h : c
  · simpa only [if_pos h] using hx
  · simpa only [if_neg h] using hy

theorem tryCatch_apply {σ α : Type} (x : PyM σ α) (h : PyErr → PyM σ α) (s : σ) :
    (tryCatch x h) s = (match x s with
      | .error l => .error l
      | .ok (.error e, s') => h e s'
      | .ok (.ok a, s') => .ok (.ok a, s')) := by
  cases hx : x s with
  | error l =>
      simp [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch, ExceptT.mk,
            Bind.bind, StateT.bind, hx, Except.bind]
  | ok p =>
      obtain ⟨r, s'⟩ := p
      cases r with
      | error e =>
          simp [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch, ExceptT.mk,
                Bind.bind, StateT.bind, hx, Except.bind]
      | ok a =>
          simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch,
                     ExceptT.mk, Bind.bind, StateT.bind, hx, Except.bind]
          rfl

theorem PyLe.tryCatch {σ α : Type} {x x' : PyM σ α} {h h' : PyErr → PyM σ α}
    (hx : x ⊑ₚ x') (hh : ∀ e, h e ⊑ₚ h' e) :
    (tryCatch x h) ⊑ₚ (tryCatch x' h') := by
  rw [PyLe_iff]; intro s
  rw [tryCatch_apply, tryCatch_apply]
  rcases PyLe_iff.mp hx s with hs | hs
  · rw [hs]; left; rfl
  · rw [hs]
    rcases hx' : x' s with l | ⟨r, s'⟩
    · right; rfl
    · cases r with
      | error e => exact PyLe_iff.mp (hh e) s'
      | ok a => right; rfl

theorem PyLe.zoomIn {S W α : Type} (get : S → W) (put : S → W → S)
    {x y : PyM W α} (h : x ⊑ₚ y) :
    (LeanModels.zoomIn get put x : PyM S α) ⊑ₚ LeanModels.zoomIn get put y := by
  rw [PyLe_iff]; intro s
  simp only [LeanModels.zoomIn]
  rcases PyLe_iff.mp h (get s) with hs | hs
  · rw [hs]; left; rfl
  · rw [hs]; right; rfl

theorem PyLe.zoomOut {S W α : Type} (mk : W → S) (prj : S → W)
    {x y : PyM S α} (h : x ⊑ₚ y) :
    (LeanModels.zoomOut mk prj x : PyM W α) ⊑ₚ LeanModels.zoomOut mk prj y := by
  rw [PyLe_iff]; intro w
  simp only [LeanModels.zoomOut]
  rcases PyLe_iff.mp h (mk w) with hs | hs
  · rw [hs]; left; rfl
  · rw [hs]; right; rfl

theorem PyLe.inFrame {α : Type} {x y : SemW α} (h : x ⊑ₚ y) :
    inFrame x ⊑ₚ inFrame y := PyLe.zoomIn _ _ h

theorem PyLe.inWorld {α : Type} (locals : REnv) {x y : SemF α} (h : x ⊑ₚ y) :
    inWorld locals x ⊑ₚ inWorld locals y := PyLe.zoomOut _ _ h

/-- THE SIXTH SHAPE: the pure-worker seam. `liftRes` is the single door the
maximal trunk comes through, so `Res.le` on a fueled trunk worker becomes
`⊑ₚ` here — this is what carries `setDedup_mono` and `evalCompareOpH_mono`
across, and it is the only place `K.fuel` monotonicity is consumed. -/
theorem PyLe.liftRes {σ α : Type} {x y : Res α} (h : x ⊑ y) :
    (liftRes x : PyM σ α) ⊑ₚ liftRes y := by
  rcases h with h | h
  · subst h; rw [PyLe_iff]; intro s; left; rfl
  · subst h; exact PyLe.refl' _

/-! ## §0.5 THE WALKER

**SYNTAX-DIRECTED BY CONSTRUCTION, and the construction is `repeat'` rather
than recursion.** Three properties earn their keep, and each was bought with a
measured failure:

1. **`repeat'` takes ONE step per goal and KEEPS it.** A recursive macro whose
   body is a backtracking `first` re-plans an entire subtree whenever a leaf
   below it fails — linear on `bind` spines, exponential on `ite` chains, and
   `applyBuiltin`'s 19-deep chain timed out at 200 000 heartbeats. A failure at
   a leaf must be an OPEN LEAF, never a parent that reconsiders.
2. **The leaf closer runs FIRST, guarded by `done`.** `apply` unifies at
   DEFAULT transparency, so `apply PyLe.ite` will happily whnf-unfold a tier
   constant to find an `ite` underneath it — which is how a walker descends
   THROUGH `applyBuiltin` instead of stopping at `applyBuiltin_mono`. Running
   the named lemma first is what makes a factored proof stay factored, and
   `done` is what stops a partial application from committing.
3. **The early reflexivity check is `with_reducible`.** It must succeed on
   syntactically equal subtrees and FAIL FAST otherwise; at default
   transparency `isDefEq` on two 200-line bodies that differ only in `K` tries
   to reconcile them by unfolding, and that reconciliation is what "timed out
   at whnf" actually was.

`raise the heartbeats` is not on the list: it trades a wrong answer for a slow
one. Everything in this file closes under `mono_with`/`mono_kont` at the
default 200 000. -/

scoped syntax "mono_with" tacticSeq : tactic
macro_rules
  | `(tactic| mono_with $leaf) =>
    `(tactic|
        (repeat' (first
           | (with_reducible exact PyLe.refl' _)
           | (($leaf); done)
           | apply PyLe.bind
           | apply PyLe.ite
           | apply PyLe.tryCatch
           | apply PyLe.inFrame
           | apply PyLe.inWorld
           | apply PyLe.zoomIn
           | apply PyLe.zoomOut
           | intro _
           | split)
         all_goals (first | exact PyLe.refl' _ | ($leaf))))

/-! ## §0.6 THE ORDER ON THE CONTINUATION RECORD -/

/-- Fieldwise order on `Kont`, PLUS the bound.

`K.fuel` is not a function field and it is load-bearing: the fuel-free half is
fuel-free in its RECURSION, not in its ARGUMENTS. It is read at TWO sites —
`evalCompareOpH h K.fuel op lhs rhs` in `evalCompareChainM` (Eval.lean:963) and
`setDedup (← frameHeap) K.fuel [] xs` in `applyBuiltin`'s `set` arm
(Eval.lean:392) — where it bounds the trunk's fuel-TAKING pure workers. So a
fieldwise order over the 13 FUNCTION fields alone is too weak; carrying
`K.fuel ≤ K'.fuel` STRENGTHENS the relation and weakens no definition. -/
def KontLe (K K' : Kont) : Prop :=
  K.fuel ≤ K'.fuel ∧
  (∀ f args, K.call f args ⊑ₚ K'.call f args) ∧
  (∀ e a args, K.callClo e a args ⊑ₚ K'.callClo e a args) ∧
  (∀ ks vs, K.dictItems ks vs ⊑ₚ K'.dictItems ks vs) ∧
  (∀ kws, K.kwArgs kws ⊑ₚ K'.kwArgs kws) ∧
  (∀ t b o, K.whileLoop t b o ⊑ₚ K'.whileLoop t b o) ∧
  (∀ t xs b, K.forSeq t xs b ⊑ₚ K'.forSeq t xs b) ∧
  (∀ t a i b, K.forList t a i b ⊑ₚ K'.forList t a i b) ∧
  (∀ t a i n sv kd b, K.forDict t a i n sv kd b ⊑ₚ K'.forDict t a i n sv kd b) ∧
  (∀ a, K.stepIter a ⊑ₚ K'.stepIter a) ∧
  (∀ k, K.execGen k ⊑ₚ K'.execGen k) ∧
  (∀ t a b, K.forGen t a b ⊑ₚ K'.forGen t a b) ∧
  (∀ a, K.drainIter a ⊑ₚ K'.drainIter a) ∧
  (∀ a b, K.anyAllIter a b ⊑ₚ K'.anyAllIter a b)

/-! ## §1 THE PRE-BLOCK HELPERS — in dependency order -/

set_option maxRecDepth 8000 in
theorem iterValues_mono (K K' : Kont) (hK : KontLe K K') (m : Module)
    (fname : String) (g : Bool) :
    ∀ v, iterValues K m fname g v ⊑ₚ iterValues K' m fname g v := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdrain, hanyAll⟩ := hK
  intro v
  simp only [iterValues]
  mono_with (first | exact hdrain _ | exact hanyAll _ _ | assumption)

set_option maxRecDepth 8000 in
theorem applyBuiltin_mono (K K' : Kont) (hK : KontLe K K') (m : Module)
    (fname : String) (vs : List RVal) :
    applyBuiltin K m fname vs ⊑ₚ applyBuiltin K' m fname vs := by
  have hIV := iterValues_mono K K' hK m
  obtain ⟨hfuel, hcall, hcallClo, _, _, _, _, _, _, hstepIter, _, _, hdrain, hanyAll⟩ := hK
  unfold applyBuiltin
  mono_with (first
    | exact hdrain _
    | exact hanyAll _ _
    | exact hstepIter _
    | exact hIV _ _ _
    | exact PyLe.liftRes (setDedup_mono hfuel _)
    | assumption)

set_option maxRecDepth 8000 in
theorem applyAttrPlan_mono (K K' : Kont) (hK : KontLe K K') (a : Addr) (attr : String) :
    ∀ (p : AttrPlan) (vs : List RVal),
      applyAttrPlan K a attr p vs ⊑ₚ applyAttrPlan K' a attr p vs := by
  obtain ⟨_, hcall, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hK
  intro p vs
  unfold applyAttrPlan
  mono_with (first | exact hcall _ _ | assumption)

set_option maxRecDepth 8000 in
theorem applyStrMethod_mono (sv : String) :
    ∀ (p : StrPlan) (vs : List RVal),
      applyStrMethod sv p vs ⊑ₚ applyStrMethod sv p vs :=
  fun _ _ => PyLe.refl' _

set_option maxRecDepth 8000 in
theorem applyCallPlan_mono (K K' : Kont) (hK : KontLe K K') (m : Module) :
    ∀ (p : CallPlan) (vs : List RVal),
      applyCallPlan K m p vs ⊑ₚ applyCallPlan K' m p vs := by
  have hAB := applyBuiltin_mono K K' hK m
  obtain ⟨_, hcall, hcallClo, _, _, _, _, _, _, _, _, _, _, _⟩ := hK
  intro p vs
  unfold applyCallPlan
  mono_with (first
    | exact hAB _ _
    | exact hcall _ _
    | exact hcallClo _ _ _
    | assumption)

/-! ## §2 THE FUEL-FREE EXPRESSION HALF

One `mutual_induct`, four conjuncts, ONE uniform tactic over all 31 arms. The
leaf list is the `Kont` fields the arms reach plus the two seams the fuel BOUND
comes through (`PyLe.liftRes` over `evalCompareOpH_mono`). -/

set_option maxRecDepth 8000 in
theorem evalOpen_monoAll (K K' : Kont) (hK : KontLe K K') (m : Module) :
    (∀ e : Expr, evalOpen K m e ⊑ₚ evalOpen K' m e) ∧
    (∀ es : List Expr, evalOpenList K m es ⊑ₚ evalOpenList K' m es) ∧
    (∀ (lhs : RVal) (ops : List CmpOp) (es : List Expr),
        evalCompareChainM K m lhs ops es ⊑ₚ evalCompareChainM K' m lhs ops es) ∧
    (∀ (op : BoolOp) (es : List Expr),
        evalBoolChainM K m op es ⊑ₚ evalBoolChainM K' m op es) := by
  have hCP := applyCallPlan_mono K K' hK m
  have hAP := applyAttrPlan_mono K K' hK
  obtain ⟨hfuel, hcall, hcallClo, hdictItems, hkwArgs, hwhile, hforSeq, hforList,
          hforDict, hstepIter, hexecGen, hforGen, hdrain, hanyAll⟩ := hK
  apply evalOpen.mutual_induct
    (motive_1 := fun e => evalOpen K m e ⊑ₚ evalOpen K' m e)
    (motive_2 := fun es => evalOpenList K m es ⊑ₚ evalOpenList K' m es)
    (motive_3 := fun lhs ops es =>
        evalCompareChainM K m lhs ops es ⊑ₚ evalCompareChainM K' m lhs ops es)
    (motive_4 := fun op es => evalBoolChainM K m op es ⊑ₚ evalBoolChainM K' m op es)
  all_goals intros
  all_goals
    (try simp only [evalOpen, evalOpenList, evalBoolChainM, evalCompareChainM])
  all_goals
    mono_with (first
      | exact hCP _ _
      | exact hAP _ _ _ _
      | exact hcall _ _
      | exact hcallClo _ _ _
      | exact hdictItems _ _
      | exact hkwArgs _
      | exact hwhile _ _ _
      | exact hforSeq _ _ _
      | exact hforList _ _ _ _
      | exact hforDict _ _ _ _ _ _ _
      | exact hstepIter _
      | exact hexecGen _
      | exact hforGen _ _ _
      | exact hdrain _
      | exact hanyAll _ _
      | exact PyLe.liftRes (evalCompareOpH_mono hfuel)
      | assumption
      | apply_assumption)

theorem evalOpen_mono (K K' : Kont) (hK : KontLe K K') (m : Module) :
    ∀ e : Expr, evalOpen K m e ⊑ₚ evalOpen K' m e := (evalOpen_monoAll K K' hK m).1

theorem evalOpenList_mono (K K' : Kont) (hK : KontLe K K') (m : Module) :
    ∀ es : List Expr, evalOpenList K m es ⊑ₚ evalOpenList K' m es :=
  (evalOpen_monoAll K K' hK m).2.1

theorem evalCompareChainM_mono (K K' : Kont) (hK : KontLe K K') (m : Module) :
    ∀ (lhs : RVal) (ops : List CmpOp) (es : List Expr),
      evalCompareChainM K m lhs ops es ⊑ₚ evalCompareChainM K' m lhs ops es :=
  (evalOpen_monoAll K K' hK m).2.2.1

theorem evalBoolChainM_mono (K K' : Kont) (hK : KontLe K K') (m : Module) :
    ∀ (op : BoolOp) (es : List Expr),
      evalBoolChainM K m op es ⊑ₚ evalBoolChainM K' m op es :=
  (evalOpen_monoAll K K' hK m).2.2.2

/-! ## §3 THE FUEL-FREE STATEMENT HALF -/

set_option maxRecDepth 8000 in
theorem execOpen_monoAll (K K' : Kont) (hK : KontLe K K') (m : Module) :
    (∀ st : Stmt, execOpen K m st ⊑ₚ execOpen K' m st) ∧
    (∀ ss : List Stmt, execOpenList K m ss ⊑ₚ execOpenList K' m ss) := by
  have hE := evalOpen_mono K K' hK m
  have hEL := evalOpenList_mono K K' hK m
  have hCC := evalCompareChainM_mono K K' hK m
  have hBC := evalBoolChainM_mono K K' hK m
  have hCP := applyCallPlan_mono K K' hK m
  have hAP := applyAttrPlan_mono K K' hK
  obtain ⟨hfuel, hcall, hcallClo, hdictItems, hkwArgs, hwhile, hforSeq, hforList,
          hforDict, hstepIter, hexecGen, hforGen, hdrain, hanyAll⟩ := hK
  apply execOpen.mutual_induct
    (motive_1 := fun st => execOpen K m st ⊑ₚ execOpen K' m st)
    (motive_2 := fun ss => execOpenList K m ss ⊑ₚ execOpenList K' m ss)
  all_goals intros
  all_goals (try simp only [execOpen, execOpenList])
  all_goals
    mono_with (first
      | exact hE _
      | exact hEL _
      | exact hCC _ _ _
      | exact hBC _ _
      | exact hCP _ _
      | exact hAP _ _ _ _
      | exact hcall _ _
      | exact hcallClo _ _ _
      | exact hdictItems _ _
      | exact hkwArgs _
      | exact hwhile _ _ _
      | exact hforSeq _ _ _
      | exact hforList _ _ _ _
      | exact hforDict _ _ _ _ _ _ _
      | exact hstepIter _
      | exact hexecGen _
      | exact hforGen _ _ _
      | exact hdrain _
      | exact hanyAll _ _
      | exact PyLe.liftRes (evalCompareOpH_mono hfuel)
      | assumption
      | apply_assumption)

theorem execOpen_mono (K K' : Kont) (hK : KontLe K K') (m : Module) :
    ∀ st : Stmt, execOpen K m st ⊑ₚ execOpen K' m st := (execOpen_monoAll K K' hK m).1

theorem execOpenList_mono (K K' : Kont) (hK : KontLe K K') (m : Module) :
    ∀ ss : List Stmt, execOpenList K m ss ⊑ₚ execOpenList K' m ss :=
  (execOpen_monoAll K K' hK m).2

/-! ## §4 THE FUELED KNOT -/

theorem PyLe.exhausted_le {σ α : Type} (y : PyM σ α) : (exhausted : PyM σ α) ⊑ₚ y :=
  PyLe_iff.mpr fun _ => Or.inl rfl

/-- `Kont.bottom` is the bottom of the fieldwise order: every operation is
`.timeout`, which is `⊑ₚ` everything. This is `kont m 0`, and it is why fuel
exhaustion is loud rather than wrong. -/
theorem KontLe.bottom (K' : Kont) : KontLe Kont.bottom K' :=
  ⟨Nat.zero_le _,
   fun _ _ => PyLe.exhausted_le _, fun _ _ _ => PyLe.exhausted_le _,
   fun _ _ => PyLe.exhausted_le _, fun _ => PyLe.exhausted_le _,
   fun _ _ _ => PyLe.exhausted_le _, fun _ _ _ => PyLe.exhausted_le _,
   fun _ _ _ _ => PyLe.exhausted_le _, fun _ _ _ _ _ _ _ => PyLe.exhausted_le _,
   fun _ => PyLe.exhausted_le _, fun _ => PyLe.exhausted_le _,
   fun _ _ _ => PyLe.exhausted_le _, fun _ => PyLe.exhausted_le _,
   fun _ _ => PyLe.exhausted_le _⟩

/-- The uniform leaf closer for every `Kont`-parameterised lemma: the two
pure-worker seams the fuel BOUND comes through, then the context. `hf` is the
`K.fuel ≤ K'.fuel` hypothesis, passed by name because a macro is hygienic. -/
scoped syntax "mono_kont" ident : tactic
macro_rules
  | `(tactic| mono_kont $hf) =>
    `(tactic| mono_with (first
        | exact PyLe.liftRes (evalCompareOpH_mono $hf)
        | exact PyLe.liftRes (setDedup_mono $hf _)
        | assumption
        | apply_assumption))

set_option maxRecDepth 8000 in
theorem kwArgsAt_mono (K K' : Kont) (hK : KontLe K K') (m : Module) :
    ∀ kws, kwArgsAt K m kws ⊑ₚ kwArgsAt K' m kws := by
  have hE := evalOpen_mono K K' hK m
  obtain ⟨hfuel, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hK
  intro kws
  induction kws with
  | nil => simp only [kwArgsAt]; exact PyLe.refl' _
  | cons p rest ih =>
      obtain ⟨n, e⟩ := p
      simp only [kwArgsAt]
      mono_kont hfuel

set_option maxRecDepth 8000 in
theorem dictItemsAt_mono (K K' : Kont) (hK : KontLe K K') (m : Module) :
    ∀ ks vs, dictItemsAt K m ks vs ⊑ₚ dictItemsAt K' m ks vs := by
  have hE := evalOpen_mono K K' hK m
  obtain ⟨hfuel, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hK
  intro ks
  induction ks with
  | nil => intro vs; cases vs <;> (simp only [dictItemsAt]; exact PyLe.refl' _)
  | cons k ks ih =>
      intro vs
      cases vs with
      | nil => simp only [dictItemsAt]; exact PyLe.refl' _
      | cons v vs => simp only [dictItemsAt]; mono_kont hfuel

set_option maxRecDepth 8000 in
theorem stepIterAt_mono (K K' : Kont) (hK : KontLe K K') :
    ∀ a, stepIterAt K a ⊑ₚ stepIterAt K' a := by
  obtain ⟨hfuel, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hK
  intro a
  unfold stepIterAt
  mono_kont hfuel

set_option maxRecDepth 8000 in
theorem execGenAt_mono (K K' : Kont) (hK : KontLe K K') (m : Module) :
    ∀ k, execGenAt K m k ⊑ₚ execGenAt K' m k := by
  have hE := evalOpen_mono K K' hK m
  have hEL := execOpenList_mono K K' hK m
  have hS := execOpen_mono K K' hK m
  obtain ⟨hfuel, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hK
  intro k
  unfold execGenAt
  mono_kont hfuel

set_option maxRecDepth 8000 in
theorem forGenAt_mono (K K' : Kont) (hK : KontLe K K') (m : Module) :
    ∀ target a body, forGenAt K m target a body ⊑ₚ forGenAt K' m target a body := by
  have hEL := execOpenList_mono K K' hK m
  obtain ⟨hfuel, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hK
  intro target a body
  unfold forGenAt
  mono_kont hfuel

set_option maxRecDepth 8000 in
theorem drainIterAt_mono (K K' : Kont) (hK : KontLe K K') :
    ∀ a, drainIterAt K a ⊑ₚ drainIterAt K' a := by
  obtain ⟨hfuel, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hK
  intro a
  unfold drainIterAt
  mono_kont hfuel

set_option maxRecDepth 8000 in
theorem anyAllIterAt_mono (K K' : Kont) (hK : KontLe K K') :
    ∀ a b, anyAllIterAt K a b ⊑ₚ anyAllIterAt K' a b := by
  obtain ⟨hfuel, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hK
  intro a b
  unfold anyAllIterAt
  mono_kont hfuel

set_option maxRecDepth 8000 in
theorem callCloAt_mono (K K' : Kont) (hK : KontLe K K') (m : Module) :
    ∀ name params argsOk localsOk isGen body captured args,
      callCloAt K m name params argsOk localsOk isGen body captured args
        ⊑ₚ callCloAt K' m name params argsOk localsOk isGen body captured args := by
  have hEL := execOpenList_mono K K' hK m
  obtain ⟨hfuel, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hK
  intro name params argsOk localsOk isGen body captured args
  unfold callCloAt
  mono_kont hfuel

set_option maxRecDepth 8000 in
theorem callInM_mono (K K' : Kont) (hK : KontLe K K') (m : Module) :
    ∀ fname args, callInM K m fname args ⊑ₚ callInM K' m fname args := by
  have hEL := execOpenList_mono K K' hK m
  obtain ⟨hfuel, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hK
  intro fname args
  unfold callInM
  mono_kont hfuel

/-! ## §5 THE THEOREM -/

/-- **Fuel monotonicity for the monadic rebuild**, stated where the fuel lives:
`kont m` is monotone in fuel for the fieldwise order on `Kont`. Induction is on
FUEL, which is the framework's own exemption to the house rule (`fuelMono`,
`Obs.lean`); every consumer above it inducts on syntax instead.

Read with `evalOpen_mono`/`execOpen_mono`: those say the fuel-FREE half is
monotone in the CONTINUATION, this says the continuation is monotone in the
fuel, and the composition is the whole interpreter. -/
theorem kontMono (m : Module) : ∀ (f f' : Nat), f ≤ f' → KontLe (kont m f) (kont m f') := by
  intro f
  induction f with
  | zero => intro f' _; simp only [kont]; exact KontLe.bottom _
  | succ f ih =>
    intro f' hf
    cases f' with
    | zero => exact absurd hf (Nat.not_succ_le_zero f)
    | succ g =>
      have hk : f ≤ g := Nat.le_of_succ_le_succ hf
      have IH := ih g hk
      have hCI := callInM_mono _ _ IH m
      have hCC := callCloAt_mono _ _ IH m
      have hDI := dictItemsAt_mono _ _ IH m
      have hKW := kwArgsAt_mono _ _ IH m
      have hSI := stepIterAt_mono _ _ IH
      have hEG := execGenAt_mono _ _ IH m
      have hFG := forGenAt_mono _ _ IH m
      have hDR := drainIterAt_mono _ _ IH
      have hAA := anyAllIterAt_mono _ _ IH
      have hE := evalOpen_mono _ _ IH m
      have hEL := execOpenList_mono _ _ IH m
      obtain ⟨hfuel, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := IH
      refine ⟨hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals intros
      all_goals simp only [kont]
      all_goals mono_kont hfuel

/-- **THE THEOREM the ∃F collapse is waiting on** (`docs/backlog/pyrebuild.md`
§Owed): a monadic run that DECIDED keeps its exact outcome at any higher fuel.
Stated at the runner boundary, in the trunk's own `⊑ʳ` so `callInMono`'s
consumers compare like for like with `callIn_mono`. -/
theorem toRun_le {σ α : Type} {x y : PyM σ α} (h : x ⊑ₚ y) (s : σ) :
    toRun x s ⊑ʳ toRun y s := by
  rcases PyLe_iff.mp h s with hs | hs
  · left; simp only [toRun, hs]
  · right; simp only [toRun, hs]

theorem fuelMono (m : Module) (fuel fuel' : Nat) (hf : fuel ≤ fuel')
    (w : World) (fname : String) (args : Array RVal) :
    callInMono m fuel w fname args ⊑ʳ callInMono m fuel' w fname args :=
  toRun_le (((kontMono m fuel fuel' hf).2.1) fname args) w

/-- The same fact one layer in, for consumers that keep the rebuild's own
`RefusalCause` and snapshot rather than the trunk-shaped projection. -/
theorem call_fuelMono (m : Module) (fuel fuel' : Nat) (hf : fuel ≤ fuel')
    (fname : String) (args : Array RVal) :
    (kont m fuel).call fname args ⊑ₚ (kont m fuel').call fname args :=
  ((kontMono m fuel fuel' hf).2.1) fname args

/-! ## §6 THE AXIOM LEDGER

House style for `Monadic/`: the prints live in the file, so the build log
carries them and they cannot go stale. §5.4a is unchanged by that — a print
here is the tree's record, and the EVIDENCE a lane quotes is
`tools/check.sh --axioms`'s verdict line from a zero-error elaboration. -/

#print axioms PyLe_iff_flatLe
#print axioms PyLe.bind
#print axioms PyLe.ite
#print axioms PyLe.tryCatch
#print axioms PyLe.zoomIn
#print axioms PyLe.zoomOut
#print axioms PyLe.liftRes
#print axioms iterValues_mono
#print axioms applyBuiltin_mono
#print axioms applyAttrPlan_mono
#print axioms applyCallPlan_mono
#print axioms evalOpen_mono
#print axioms evalOpenList_mono
#print axioms evalCompareChainM_mono
#print axioms evalBoolChainM_mono
#print axioms execOpen_mono
#print axioms execOpenList_mono
#print axioms kwArgsAt_mono
#print axioms dictItemsAt_mono
#print axioms stepIterAt_mono
#print axioms execGenAt_mono
#print axioms forGenAt_mono
#print axioms drainIterAt_mono
#print axioms anyAllIterAt_mono
#print axioms callCloAt_mono
#print axioms callInM_mono
#print axioms kontMono
#print axioms toRun_le
#print axioms call_fuelMono
#print axioms fuelMono

end LeanModels.Python.Monadic
