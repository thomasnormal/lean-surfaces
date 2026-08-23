-- LEGACY: statement target of pre-rebuild theorems; compiles, refuses what
-- it does not implement, gains no consumers; deleted when re-founded.
import LeanModels.Core.Order
import LeanModels.Python.Logic

/-!
# Fuel monotonicity and cross-fuel determinism (`LeanModels.Python`)

The enabling theorems for the `Obs` spine (docs/spec-surface.md §10): adding
fuel never changes a decided (non-`timeout`) interpreter result. This is what
makes the fuel parameter a pure implementation detail — any two runs that
decide, at any two fuels, decide identically, so `CallsTo` is functional and
the strengthened partial judgment `~~>` becomes stateable.

Since the H1 core re-shape the mutual block is `Run`-typed (state is data:
the decided outcome CONTAINS the final `FrameState`/`World`, and
monotonicity is in fuel only — a decided state survives fuel increase
exactly like a decided value), and the public `callFunction` is a
non-recursive wrapper. Structure:

* `Res.le` (`x ⊑ y`) — the flat approximation order on public results, and
  `Run.le` (`x ⊑ʳ y`) — the same order on `Run`-typed outcomes. Fuel-indexed
  runs form a chain in them.
* `fuelMono` — THE theorem: one conjunction over all nine functions of the
  interpreter's mutual block (`evalExpr`, `evalExprs`, `evalBoolChain`,
  `evalCompareChain`, `execStmt`, `execStmts`, `execWhile`, `callIn`,
  `execFor`), proved by a single induction on fuel. Each case is symbolic
  execution of one interpreter step, glued by the congruence lemmas
  `Run.le_bind` / `Run.le_ite` / `Run.le_withLocals` / `Run.le_toWorld`
  (every fuel-free helper is `⊑ʳ`-reflexive, every recursive call is the
  induction hypothesis at the decremented fuel).
* `evalExpr_mono` … `callIn_mono`, `execFor_mono` — the per-function
  corollaries in implication form, and `callFunction_mono` — the public
  monotonicity, derived through the wrapper decomposition (thaw and freeze
  are fuel-free; the only fuel inside the wrapper is `callIn`'s).
* `callFunction_det` — cross-fuel determinism; `CallsTo.functional` /
  `CallsTo.not_raises` — the spec-level consequences.
* `PyOut` / `Obs` — the observation spine itself (docs/spec-surface.md §10):
  the four-way outcome partition of a call, with fuel confined inside the
  judgment; `Obs.det` (at most one outcome, stuck *messages included*) and
  `Obs.total` (at least one, classically), hence `Obs.existsUnique` — the
  outcome is a well-defined denotation of the call.
-/

namespace LeanModels.Python

/-! ## The approximation order on results -/

/-- Flat approximation order on public interpreter results: `x ⊑ y` iff `x`
is `timeout` (the run gave up) or `x = y` (the run decided, and `y` agrees). -/
protected def Res.le {α : Type} (x y : Res α) : Prop :=
  x = .timeout ∨ x = y

@[inherit_doc] scoped infix:50 " ⊑ " => Res.le

theorem Res.le_iff {α : Type} {x y : Res α} :
    x ⊑ y ↔ (x = .timeout ∨ x = y) := Iff.rfl

theorem Res.le_refl {α : Type} (x : Res α) : x ⊑ x := Or.inr rfl

theorem Res.timeout_le {α : Type} (y : Res α) : (.timeout : Res α) ⊑ y :=
  Or.inl rfl

/-- A decided (non-`timeout`) lower bound is already the value: `⊑` collapses
to equality. This is the extraction step of every `_mono` corollary. -/
theorem Res.le_eq {α : Type} {x y : Res α} (h : x ⊑ y) (hx : x ≠ .timeout) :
    x = y := (Res.le_iff.mp h).resolve_left hx

/-- **`Res.le` IS Core's flat order** (`LeanModels/Core/Order.lean`), and this
`Iff.rfl` is the whole bridge. Stated as an iff rather than as a redefinition on
purpose: `Res.le`'s spelling, its `⊑` notation and its consumers all stay put,
and the tree gains the shared name additively. The congruences below stay
tier-local — `Sv.Res` and `Python.Res` are different types, so `le_bind` and
`le_ite` are each tier's own. -/
theorem Res.le_iff_flatLe {α : Type} {x y : Res α} :
    x ⊑ y ↔ FlatLe .timeout x y := Iff.rfl

/-- Congruence of `⊑` under `bind`: run the prefix (IH), then the
continuation pointwise (IH again, or reflexivity for fuel-free tails). -/
theorem Res.le_bind {α β : Type} {x x' : Res α} {f f' : α → Res β}
    (hx : x ⊑ x') (hf : ∀ a, f a ⊑ f' a) : (x >>= f) ⊑ (x' >>= f') := by
  rcases hx with h | h
  · subst h; exact Or.inl rfl
  · subst h
    cases x with
    | ok a => exact hf a
    | exn e => exact Or.inr rfl
    | timeout => exact Or.inl rfl
    | unsupported msg => exact Or.inr rfl

/-- Congruence of `⊑` under `if`: same condition on both sides, each branch
by its own proof. -/
theorem Res.le_ite {α : Type} {c : Prop} [Decidable c] {x x' y y' : Res α}
    (hx : x ⊑ x') (hy : y ⊑ y') :
    (if c then x else y) ⊑ (if c then x' else y') := by
  by_cases h : c
  · simpa only [if_pos h] using hx
  · simpa only [if_neg h] using hy

/-! ## The approximation order on `Run`-typed outcomes

State is data: `x ⊑ʳ y` compares whole outcomes — final state, value, error,
message and all. `fuelMono` shows every function of the mutual block is
monotone in fuel wrt `⊑ʳ`: a run that decided keeps its exact outcome
(state included) at any higher fuel. -/

/-- Flat approximation order on `Run`-typed outcomes. -/
protected def Run.le {σ α : Type} (x y : Run σ α) : Prop :=
  x = .timeout ∨ x = y

@[inherit_doc] scoped infix:50 " ⊑ʳ " => Run.le

theorem Run.le_iff {σ α : Type} {x y : Run σ α} :
    x ⊑ʳ y ↔ (x = .timeout ∨ x = y) := Iff.rfl

theorem Run.le_refl {σ α : Type} (x : Run σ α) : x ⊑ʳ x := Or.inr rfl

theorem Run.timeout_le {σ α : Type} (y : Run σ α) :
    (.timeout : Run σ α) ⊑ʳ y := Or.inl rfl

/-- A decided (non-`timeout`) lower bound is already the outcome. -/
theorem Run.le_eq {σ α : Type} {x y : Run σ α} (h : x ⊑ʳ y)
    (hx : x ≠ .timeout) : x = y := (Run.le_iff.mp h).resolve_left hx

/-- The same bridge for the state-carrying order — the fourth instance of the
one shape. -/
theorem Run.le_iff_flatLe {σ α : Type} {x y : Run σ α} :
    x ⊑ʳ y ↔ FlatLe .timeout x y := Iff.rfl

/-- Congruence of `⊑ʳ` under `Run.bind`: run the prefix (IH), then the
continuation pointwise at every intermediate state. -/
theorem Run.le_bind {σ α β : Type} {x x' : Run σ α} {f f' : σ → α → Run σ β}
    (hx : x ⊑ʳ x') (hf : ∀ s a, f s a ⊑ʳ f' s a) : x.bind f ⊑ʳ x'.bind f' := by
  rcases hx with h | h
  · subst h; exact Or.inl rfl
  · subst h
    cases x with
    | ok s a => exact hf s a
    | exn s e => exact Or.inr rfl
    | timeout => exact Or.inl rfl
    | unsupported msg => exact Or.inr rfl

/-- Congruence of `⊑ʳ` under `Run.bindE` (the exceptions tier: the
stepper's close-on-exn-through-resume continuation — `fuelMono`'s glue
for the one `bindE` consumer). -/
theorem Run.le_bindE {σ α β : Type} {x x' : Run σ α} {f f' : σ → α → Run σ β}
    {g g' : σ → PyErr → Run σ β} (hx : x ⊑ʳ x')
    (hf : ∀ s a, f s a ⊑ʳ f' s a) (hg : ∀ s e, g s e ⊑ʳ g' s e) :
    x.bindE f g ⊑ʳ x'.bindE f' g' := by
  rcases hx with h | h
  · subst h; exact Or.inl rfl
  · subst h
    cases x with
    | ok s a => exact hf s a
    | exn s e => exact hg s e
    | timeout => exact Or.inl rfl
    | unsupported msg => exact Or.inr rfl

/-- Congruence of `⊑ʳ` under `if`. -/
theorem Run.le_ite {σ α : Type} {c : Prop} [Decidable c] {x x' y y' : Run σ α}
    (hx : x ⊑ʳ x') (hy : y ⊑ʳ y') :
    (if c then x else y) ⊑ʳ (if c then x' else y') := by
  by_cases h : c
  · simpa only [if_pos h] using hx
  · simpa only [if_neg h] using hy

/-- Congruence of `⊑ʳ` under `Run.withLocals` (the nested-call splice). -/
theorem Run.le_withLocals {α : Type} {l : REnv} {x x' : Run World α}
    (h : x ⊑ʳ x') : Run.withLocals l x ⊑ʳ Run.withLocals l x' := by
  rcases h with h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inr rfl

/-- Congruence of `⊑ʳ` under `Run.toWorld` (the call-return projection). -/
theorem Run.le_toWorld {α : Type} {x x' : Run FrameState α}
    (h : x ⊑ʳ x') : Run.toWorld x ⊑ʳ Run.toWorld x' := by
  rcases h with h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inr rfl

/-- Congruence of `⊑`→`⊑ʳ` under `Run.liftRes` (the fueled helper splice:
`evalCompareOpH` is fuel-dependent since H1-proper). -/
theorem Run.le_liftRes {σ α : Type} {s : σ} {x y : Res α} (h : x ⊑ y) :
    Run.liftRes s x ⊑ʳ Run.liftRes s y := by
  rcases h with h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inr rfl

/-! ## Dict-equality fuel monotonicity (the `heapEq` mutual block)

`heapEq` is the only fueled helper outside the interpreter's mutual block
(dict `==` recurses through stored values). Its monotonicity is what lets
`fuelMono`'s compare-chain case splice it. -/

/-- Fuel monotonicity for the `heapEq`/`heapEqList`/`heapEqEntries` block,
one conjunction, by induction on fuel. -/
theorem heapEqMono (fuel : Nat) :
    (∀ (h : Heap) (active : List (Addr × Addr)) (a b : RVal) (fuel' : Nat),
      fuel ≤ fuel' → heapEq h fuel active a b ⊑ heapEq h fuel' active a b) ∧
    (∀ (h : Heap) (active : List (Addr × Addr)) (as bs : List RVal) (fuel' : Nat),
      fuel ≤ fuel' → heapEqList h fuel active as bs ⊑ heapEqList h fuel' active as bs) ∧
    (∀ (h : Heap) (active : List (Addr × Addr)) (left right : List (RVal × RVal))
        (fuel' : Nat), fuel ≤ fuel' →
      heapEqEntries h fuel active left right ⊑ heapEqEntries h fuel' active left right) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · exact fun h active a b fuel' _ => Or.inl (by simp [heapEq])
    · exact fun h active as bs fuel' _ => Or.inl (by simp [heapEqList])
    · exact fun h active l r fuel' _ => Or.inl (by simp [heapEqEntries])
  | succ fuel ih =>
    obtain ⟨ihE, ihL, ihN⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro h active a b fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases a <;> cases b <;> simp only [heapEq] <;>
          try exact Res.le_refl _
        -- remaining: tuple/tuple, listV/listV, the tuple/namedtuple square
        -- (elementwise), ref/ref (dicts)
        case tuple.tuple xs ys => exact ihL h active xs.toList ys.toList k hk
        case listV.listV xs ys => exact ihL h active xs.toList ys.toList k hk
        case ntuple.ntuple tn1 fs1 xs tn2 fs2 ys =>
          exact ihL h active xs.toList ys.toList k hk
        case ntuple.tuple tn1 fs1 xs ys =>
          exact ihL h active xs.toList ys.toList k hk
        case tuple.ntuple xs tn2 fs2 ys =>
          exact ihL h active xs.toList ys.toList k hk
        case ref.ref x y =>
          refine Res.le_ite (Res.le_refl _) (Res.le_ite (Res.le_refl _) ?_)
          cases hx : Heap.get? h x with
          | none =>
            cases Heap.get? h y <;> exact Res.le_refl _
          | some o1 =>
            cases Heap.get? h y with
            | none => cases o1 <;> exact Res.le_refl _
            | some o2 =>
              cases o1 with
              | cell cv => cases o2 <;> exact Res.le_refl _
              | dict es v1 =>
                cases o2 with
                | dict fs v2 =>
                  exact Res.le_ite (ihN h ((x, y) :: active) es.toList fs.toList k hk)
                    (Res.le_refl _)
                | list ys => exact Res.le_refl _
                | «instance» ci attrs => exact Res.le_refl _
                | generator qn lo kk stt => exact Res.le_refl _
                | cell cv => exact Res.le_refl _
                | closure nm ps ao lo' hg ig bd cap => exact Res.le_refl _
                | pyset zs => exact Res.le_refl _
              | list xs =>
                cases o2 with
                | dict fs v2 => exact Res.le_refl _
                | list ys =>
                  exact Res.le_ite (ihL h ((x, y) :: active) xs.toList ys.toList k hk)
                    (Res.le_refl _)
                | «instance» ci attrs => exact Res.le_refl _
                | generator qn lo kk stt => exact Res.le_refl _
                | cell cv => exact Res.le_refl _
                | closure nm ps ao lo' hg ig bd cap => exact Res.le_refl _
                | pyset zs => exact Res.le_refl _
              | «instance» ci attrs => cases o2 <;> exact Res.le_refl _
              | generator qn lo kk stt => cases o2 <;> exact Res.le_refl _
              | closure nm ps ao lo' hg ig bd cap =>
                cases o2 <;> exact Res.le_refl _
              | pyset zs => cases o2 <;> exact Res.le_refl _
    · intro h active as bs fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases as with
        | nil => cases bs <;> (simp only [heapEqList]; exact Res.le_refl _)
        | cons a as' =>
          cases bs with
          | nil => simp only [heapEqList]; exact Res.le_refl _
          | cons b bs' =>
            simp only [heapEqList]
            exact Res.le_bind (ihE h active a b k hk) fun e =>
              Res.le_ite (ihL h active as' bs' k hk) (Res.le_refl _)
    · intro h active l r fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases l with
        | nil => simp only [heapEqEntries]; exact Res.le_refl _
        | cons kv rest =>
          obtain ⟨kk, vv⟩ := kv
          simp only [heapEqEntries]
          cases dictFind r kk with
          | none => exact Res.le_refl _
          | some w =>
            exact Res.le_bind (ihE h active vv w k hk) fun e =>
              Res.le_ite (ihN h active rest r k hk) (Res.le_refl _)

/-- Fuel monotonicity of the H2 list-membership scan (elementwise
`heapEq` splices). -/
theorem heapContainsScan_mono {h : Heap} {fuel : Nat} {x : RVal}
    {l : List RVal} {fuel' : Nat} (hf : fuel ≤ fuel') :
    heapContainsScan h fuel x l ⊑ heapContainsScan h fuel' x l := by
  induction l with
  | nil => exact Res.le_refl _
  | cons v vs ih =>
    simp only [heapContainsScan]
    exact Res.le_bind ((heapEqMono fuel).1 h [] v x fuel' hf)
      fun e => Res.le_ite (Res.le_refl _) ih

/-- Fuel monotonicity for `setDedup` (H7+ set construction): the
element-equality scans thread the fuel; the accumulator generalizes. -/
theorem setDedup_mono {h : Heap} {fuel fuel' : Nat} {xs : List RVal}
    (hf : fuel ≤ fuel') :
    ∀ acc, setDedup h fuel acc xs ⊑ setDedup h fuel' acc xs := by
  induction xs with
  | nil => intro acc; exact Res.le_refl _
  | cons v vs ih =>
    intro acc
    simp only [setDedup]
    refine Res.le_ite ?_ (Res.le_refl _)
    exact Res.le_bind (heapContainsScan_mono hf) fun dup =>
      Res.le_ite (ih _) (ih _)

/-- Fuel monotonicity of heap-container membership. -/
theorem heapContains_mono {h : Heap} {fuel : Nat} {a : Addr} {k : RVal}
    {fuel' : Nat} (hf : fuel ≤ fuel') :
    heapContains h fuel a k ⊑ heapContains h fuel' a k := by
  simp only [heapContains]
  cases Heap.get? h a with
  | none => exact Res.le_refl _
  | some o =>
    cases o with
    | dict es v => exact Res.le_refl _
    | list xs => exact heapContainsScan_mono hf
    | «instance» ci attrs => exact Res.le_refl _
    | generator qn lo kk stt => exact Res.le_refl _
    | cell cv => exact Res.le_refl _
    | closure nm ps ao lo' hg ig bd cap => exact Res.le_refl _
    | pyset zs => exact Res.le_ite (heapContainsScan_mono hf) (Res.le_refl _)

/-- Fuel monotonicity of the heap deep-freeze (`freezeH`/`freezeListH`),
one conjunction by induction on fuel — the freeze leg of the public
wrapper's monotonicity decomposition (docs/memory-model.md v2). -/
theorem freezeHMono (fuel : Nat) :
    (∀ (h : Heap) (path : List Addr) (v : RVal) (fuel' : Nat), fuel ≤ fuel' →
      RVal.freezeH h fuel path v ⊑ RVal.freezeH h fuel' path v) ∧
    (∀ (h : Heap) (path : List Addr) (l : List RVal) (fuel' : Nat), fuel ≤ fuel' →
      RVal.freezeListH h fuel path l ⊑ RVal.freezeListH h fuel' path l) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · exact fun h path v fuel' _ => Or.inl (by simp [RVal.freezeH])
    · exact fun h path l fuel' _ => Or.inl (by simp [RVal.freezeListH])
  | succ fuel ih =>
    obtain ⟨ihV, ihL⟩ := ih
    refine ⟨?_, ?_⟩
    · intro h path v fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases v <;> simp only [RVal.freezeH] <;> try exact Res.le_refl _
        case listV xs =>
          exact Res.le_bind (ihL h path xs.toList k hk) fun vs => Res.le_refl _
        case tuple xs =>
          exact Res.le_bind (ihL h path xs.toList k hk) fun vs => Res.le_refl _
        case ref a =>
          refine Res.le_ite (Res.le_refl _) ?_
          cases Heap.get? h a with
          | none => exact Res.le_refl _
          | some o =>
            cases o with
            | dict es v => exact Res.le_refl _
            | «instance» ci attrs => exact Res.le_refl _
            | generator qn lo kk stt => exact Res.le_refl _
            | cell cv => exact Res.le_refl _
            | closure nm ps ao lo' hg ig bd cap => exact Res.le_refl _
            | pyset zs => exact Res.le_refl _
            | list xs =>
              exact Res.le_bind (ihL h (a :: path) xs.toList k hk)
                fun vs => Res.le_refl _
    · intro h path l fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases l with
        | nil => simp only [RVal.freezeListH]; exact Res.le_refl _
        | cons v vs =>
          simp only [RVal.freezeListH]
          exact Res.le_bind (ihV h path v k hk) fun v' =>
            Res.le_bind (ihL h path vs k hk) fun vs' => Res.le_refl _

/-- Fuel monotonicity of container membership (H5 iteration): a str
receiver is pure, every element-scanning receiver splices the H2 scan. -/
theorem valContains_mono {h : Heap} {fuel : Nat} {a b : RVal}
    {fuel' : Nat} (hf : fuel ≤ fuel') :
    valContains h fuel a b ⊑ valContains h fuel' a b := by
  cases b <;> simp only [valContains] <;> try exact Res.le_refl _
  case ref d => exact heapContains_mono hf
  case listV xs => exact heapContainsScan_mono hf
  case tuple xs => exact heapContainsScan_mono hf
  case ntuple tn fs xs => exact heapContainsScan_mono hf

/-- Fuel monotonicity of the heap-aware comparison step. -/
theorem evalCompareOpH_mono {h : Heap} {fuel : Nat} {op : CmpOp} {a b : RVal}
    {fuel' : Nat} (hf : fuel ≤ fuel') :
    evalCompareOpH h fuel op a b ⊑ evalCompareOpH h fuel' op a b := by
  cases op <;> simp only [evalCompareOpH] <;> try exact Res.le_refl _
  case eq =>
    exact Res.le_ite (Res.le_refl _) ((heapEqMono fuel).1 h [] a b fuel' hf)
  case notEq =>
    exact Res.le_ite (Res.le_refl _)
      (Res.le_bind ((heapEqMono fuel).1 h [] a b fuel' hf)
        fun e => Res.le_refl _)
  case inOp => exact valContains_mono hf
  case notIn =>
    exact Res.le_bind (valContains_mono hf) fun e => Res.le_refl _

/-! ## Fuel monotonicity — the enabling theorem -/

/-- **Fuel monotonicity**, one conjunction over the whole mutual block, by
induction on fuel: for every interpreter function `F` and `fuel ≤ fuel'`,
`F fuel ⊑ʳ F fuel'` — a run that decided keeps its exact outcome (final
state included) at any higher fuel. Conjunct order: `evalExpr`, `evalExprs`,
`evalBoolChain`, `evalCompareChain`, `execStmt`, `execStmts`, `execWhile`,
`callIn`, `execFor` (the mutual block's order — `callIn` sits where
`callFunction` sat before the H1 re-shape, keeping the projection paths of
the other corollaries stable). Consume it through the per-function `_mono`
corollaries below. -/
theorem fuelMono (fuel : Nat) :
    (∀ (m : Module) (st : FrameState) (e : Expr) (fuel' : Nat), fuel ≤ fuel' →
      evalExpr m fuel st e ⊑ʳ evalExpr m fuel' st e) ∧
    (∀ (m : Module) (st : FrameState) (es : List Expr) (fuel' : Nat), fuel ≤ fuel' →
      evalExprs m fuel st es ⊑ʳ evalExprs m fuel' st es) ∧
    (∀ (m : Module) (st : FrameState) (op : BoolOp) (e : Expr) (rest : List Expr)
        (fuel' : Nat), fuel ≤ fuel' →
      evalBoolChain m fuel st op e rest ⊑ʳ evalBoolChain m fuel' st op e rest) ∧
    (∀ (m : Module) (st : FrameState) (lhs : RVal) (ops : List CmpOp) (cs : List Expr)
        (fuel' : Nat), fuel ≤ fuel' →
      evalCompareChain m fuel st lhs ops cs ⊑ʳ evalCompareChain m fuel' st lhs ops cs) ∧
    (∀ (m : Module) (st : FrameState) (s : Stmt) (fuel' : Nat), fuel ≤ fuel' →
      execStmt m fuel st s ⊑ʳ execStmt m fuel' st s) ∧
    (∀ (m : Module) (st : FrameState) (ss : List Stmt) (fuel' : Nat), fuel ≤ fuel' →
      execStmts m fuel st ss ⊑ʳ execStmts m fuel' st ss) ∧
    (∀ (m : Module) (st : FrameState) (test : Expr) (body orelse : List Stmt)
        (fuel' : Nat), fuel ≤ fuel' →
      execWhile m fuel st test body orelse ⊑ʳ execWhile m fuel' st test body orelse) ∧
    (∀ (m : Module) (w : World) (fname : String) (args : Array RVal)
        (fuel' : Nat), fuel ≤ fuel' →
      callIn m fuel w fname args ⊑ʳ callIn m fuel' w fname args) ∧
    (∀ (m : Module) (st : FrameState) (target : Expr) (xs : List RVal)
        (body : List Stmt) (fuel' : Nat), fuel ≤ fuel' →
      execFor m fuel st target xs body ⊑ʳ execFor m fuel' st target xs body) ∧
    (∀ (m : Module) (st : FrameState) (keys values : List Expr) (fuel' : Nat),
        fuel ≤ fuel' →
      evalDictItems m fuel st keys values ⊑ʳ evalDictItems m fuel' st keys values) ∧
    (∀ (m : Module) (st : FrameState) (target : Expr) (a : Addr) (i : Nat)
        (body : List Stmt) (fuel' : Nat), fuel ≤ fuel' →
      execForList m fuel st target a i body ⊑ʳ execForList m fuel' st target a i body) ∧
    (∀ (m : Module) (st : FrameState) (a : Addr) (attr : String)
        (args : List Expr) (fuel' : Nat), fuel ≤ fuel' →
      execAttrCall m fuel st a attr args ⊑ʳ execAttrCall m fuel' st a attr args) ∧
    -- H4 (appended LAST, the recorded discipline: existing projection
    -- paths stay put): the generator stepper, the continuation walker
    -- and the lazy `for` cursor.
    (∀ (m : Module) (w : World) (a : Addr) (fuel' : Nat), fuel ≤ fuel' →
      stepIter m fuel w a ⊑ʳ stepIter m fuel' w a) ∧
    (∀ (m : Module) (st : FrameState) (k : GenCont) (fuel' : Nat), fuel ≤ fuel' →
      execGen m fuel st k ⊑ʳ execGen m fuel' st k) ∧
    (∀ (m : Module) (st : FrameState) (target : Expr) (a : Addr)
        (body : List Stmt) (fuel' : Nat), fuel ≤ fuel' →
      execForGen m fuel st target a body ⊑ʳ execForGen m fuel' st target a body) ∧
    -- H6 (appended LAST, the recorded discipline): the draining
    -- consumers' full drain and short-circuit drain
    (∀ (m : Module) (w : World) (a : Addr) (fuel' : Nat), fuel ≤ fuel' →
      drainIter m fuel w a ⊑ʳ drainIter m fuel' w a) ∧
    (∀ (m : Module) (w : World) (a : Addr) (isAll : Bool) (fuel' : Nat), fuel ≤ fuel' →
      anyAllIter m fuel w a isAll ⊑ʳ anyAllIter m fuel' w a isAll) ∧
    -- H7 (appended LAST): the closure invocation
    (∀ (m : Module) (w : World) (name : String) (params : Array Param)
        (ao lo ig : Bool) (body : Array Stmt) (cap : REnv) (args : Array RVal)
        (fuel' : Nat), fuel ≤ fuel' →
      callClosure m fuel w name params ao lo ig body cap args ⊑ʳ
        callClosure m fuel' w name params ao lo ig body cap args) := by
  induction fuel with
  | zero =>
    -- Fuel 0 is `.timeout` everywhere, the bottom of `⊑ʳ`.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun m st e fuel' _ => Or.inl (by simp [evalExpr])
    · exact fun m st es fuel' _ => Or.inl (by simp [evalExprs])
    · exact fun m st op e rest fuel' _ => Or.inl (by simp [evalBoolChain])
    · exact fun m st lhs ops cs fuel' _ => Or.inl (by simp [evalCompareChain])
    · exact fun m st s fuel' _ => Or.inl (by simp [execStmt])
    · exact fun m st ss fuel' _ => Or.inl (by simp [execStmts])
    · exact fun m st test body orelse fuel' _ => Or.inl (by simp [execWhile])
    · exact fun m w fname args fuel' _ => Or.inl (by simp [callIn])
    · exact fun m st target xs body fuel' _ => Or.inl (by simp [execFor])
    · exact fun m st keys values fuel' _ => Or.inl (by simp [evalDictItems])
    · exact fun m st target a i body fuel' _ => Or.inl (by simp [execForList])
    · exact fun m st a attr args fuel' _ => Or.inl (by simp [execAttrCall])
    · exact fun m w a fuel' _ => Or.inl (by simp [stepIter])
    · exact fun m st k fuel' _ => Or.inl (by simp [execGen])
    · exact fun m st target a body fuel' _ => Or.inl (by simp [execForGen])
    · exact fun m w a fuel' _ => Or.inl (by simp [drainIter])
    · exact fun m w a isAll fuel' _ => Or.inl (by simp [anyAllIter])
    · exact fun m w name params ao lo ig body cap args fuel' _ =>
        Or.inl (by simp [callClosure])
  | succ fuel ih =>
    obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihCall, ihFor, ihItems, ihForL,
      ihAttrC, ihStep, ihGen, ihForG, ihDrain, ihAnyAll, ihClosure⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- evalExpr
    · intro m st e fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases e with
        | constant c _ => simp only [evalExpr]; exact Run.le_refl _
        | namedExpr id v _ =>
          simp only [evalExpr]
          exact Run.le_bind (ihE m st v k hk) fun st r => Run.le_refl _
        | name id _ => simp only [evalExpr]; exact Run.le_refl _
        | binOp l op r _ =>
          simp only [evalExpr]
          exact Run.le_bind (ihE m st l k hk) fun st a =>
            Run.le_bind (ihE m st r k hk) fun st b => Run.le_refl _
        | unaryOp op operand _ =>
          simp only [evalExpr]
          exact Run.le_bind (ihE m st operand k hk) fun st v => Run.le_refl _
        | boolOp op values _ =>
          simp only [evalExpr]
          cases values.toList with
          | nil => exact Run.le_refl _
          | cons e0 es => exact ihB m st op e0 es k hk
        | compare l ops comparators _ =>
          simp only [evalExpr]
          exact Run.le_bind (ihE m st l k hk) fun st a =>
            ihC m st a ops.toList comparators.toList k hk
        | call cf cargs ckw cu _ =>
          cases cu with
          | some reason => simp only [evalExpr]; exact Run.le_refl _
          | none =>
            -- H6: unfold once, split on the keyword gate (the `cases`
            -- substitutes the scrutinee in the goal), reduce the ite,
            -- THEN fork on the callee shape
            simp only [evalExpr]
            cases hkw : ckw.isEmpty with
            | false =>
              -- ===== H6 keyword tier: positionals bind, keyword VALUES
              -- bind, the pure merge lifts, the call recurses through
              -- `callIn` (its own conjunct) =====
              simp only [Bool.false_eq_true, if_false]
              cases cf <;> try (dsimp only; exact Run.le_refl _)
              case name fname _ =>
                dsimp only
                cases Env.lookup st.locals fname with
                | some v =>
                  cases v <;>
                    exact Run.le_bind (ihEs m st cargs.toList k hk) fun st _ =>
                      Run.le_bind (ihEs m st (ckw.toList.map (·.2)) k hk) fun st _ =>
                        Run.le_refl _
                | none =>
                  cases lookupG (moduleGlobals m).1 fname with
                  | some vv =>
                    cases vv with
                    | some v =>
                      cases v <;>
                        exact Run.le_bind (ihEs m st cargs.toList k hk) fun st _ =>
                          Run.le_bind (ihEs m st (ckw.toList.map (·.2)) k hk) fun st _ =>
                            Run.le_refl _
                    | none => exact Run.le_refl _
                  | none =>
                    cases findFunction m fname with
                    | some fdefn =>
                      try dsimp only
                      refine Run.le_ite (Run.le_refl _) (Run.le_ite (Run.le_refl _) ?_)
                      refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                      refine Run.le_bind (ihEs m st (ckw.toList.map (·.2)) k hk) fun st kvs => ?_
                      refine Run.le_bind (Run.le_refl _) fun st full => ?_
                      exact Run.le_withLocals (ihCall m st.world fname full k hk)
                    | none =>
                      try dsimp only
                      -- 2026-08-13: `dict(k=v, …)` sits before `sorted`
                      -- — a positional-argument refusal, else the kwarg
                      -- values bind and the allocation is fuel-free
                      refine Run.le_ite (Run.le_refl _) (Run.le_ite (Run.le_refl _)
                        (Run.le_ite
                          (Run.le_ite (Run.le_refl _)
                            (Run.le_bind (ihEs m st (ckw.toList.map (·.2)) k hk)
                              fun st _ => Run.le_refl _))
                          (Run.le_ite ?_ (Run.le_ite (Run.le_refl _)
                            (Run.le_ite (Run.le_refl _) (Run.le_refl _))))))
                      -- sorted with keywords (H6 draining tier): key= is
                      -- a fuel-free refusal; a stray keyword binds then
                      -- raises; reverse= binds, truthiness, then the
                      -- drain / heap sort
                      refine Run.le_ite (Run.le_refl _) ?_
                      cases ckw.toList.find? (fun kv => kv.1 != "reverse") with
                      | some kv =>
                        exact Run.le_bind (ihEs m st cargs.toList k hk) fun st _ =>
                          Run.le_bind (ihEs m st (ckw.toList.map (·.2)) k hk) fun st _ =>
                            Run.le_refl _
                      | none =>
                        refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                        refine Run.le_bind (ihEs m st (ckw.toList.map (·.2)) k hk) fun st kvs => ?_
                        cases vs with
                        | nil => exact Run.le_refl _
                        | cons v vtail =>
                          cases vtail with
                          | cons _ _ => exact Run.le_refl _
                          | nil =>
                            cases kvs with
                            | nil => exact Run.le_refl _
                            | cons rv rtail =>
                              cases rtail with
                              | cons _ _ => exact Run.le_refl _
                              | nil =>
                                refine Run.le_bind (Run.le_refl _) fun st desc => ?_
                                cases v <;> try exact Run.le_refl _
                                case ref a =>
                                  dsimp only
                                  cases Heap.get? st.world.heap a with
                                  | none => exact Run.le_refl _
                                  | some obj =>
                                    cases obj <;> try exact Run.le_refl _
                                    case generator q l c stat =>
                                      refine Run.le_bind
                                        (Run.le_withLocals (ihDrain m st.world a k hk))
                                        fun st vals => ?_
                                      exact Run.le_bind (Run.le_refl _) fun st s2 =>
                                        Run.le_refl _
              case «attribute» recv attr spa =>
                dsimp only
                refine Run.le_bind (ihE m st recv k hk) fun st r => ?_
                cases r <;> try exact Run.le_refl _
                case ref a =>
                  -- H7+: instance-method keywords — plan fork, then the
                  -- merge and the call through `callIn`'s conjunct
                  dsimp only
                  cases attrCallPlan m st.world.heap a attr <;> try exact Run.le_refl _
                  case instMethod qname =>
                    dsimp only
                    cases findFunction m qname with
                    | some fdefn =>
                      try dsimp only
                      refine Run.le_ite (Run.le_refl _) ?_
                      refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                      refine Run.le_bind (ihEs m st (ckw.toList.map (·.2)) k hk) fun st kvs => ?_
                      refine Run.le_bind (Run.le_refl _) fun st full => ?_
                      exact Run.le_withLocals (ihCall m st.world qname full k hk)
                    | none => exact Run.le_refl _
                case ntuple tn fs xs =>
                  dsimp only
                  cases ntupleCallPlan m tn fs attr <;> try exact Run.le_refl _
                  case instMethod qname =>
                    dsimp only
                    cases findFunction m qname with
                    | some fdefn =>
                      try dsimp only
                      refine Run.le_ite (Run.le_refl _) ?_
                      refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                      refine Run.le_bind (ihEs m st (ckw.toList.map (·.2)) k hk) fun st kvs => ?_
                      refine Run.le_bind (Run.le_refl _) fun st full => ?_
                      exact Run.le_withLocals (ihCall m st.world qname full k hk)
                    | none => exact Run.le_refl _
            | true =>
              simp only [eq_self_iff_true, if_true]
              cases cf <;> try (dsimp only; exact Run.le_refl _)
              case «attribute» recv attr spa =>
                -- receiver-first dispatch (H3): the receiver evaluates, then
                -- `execAttrCall` forks on the pure plan (its own conjunct);
                -- an ntuple VALUE receiver (H5) forks on `ntupleCallPlan` —
                -- only the method arm recurses (args + `callIn`).
                -- Pass 6: the TRACE-CLOCK fork comes first (`isClockCall`
                -- is fuel-free, so both sides split identically; the pop
                -- and its refusals are fuel-free too).
                dsimp only
                split
                · exact Run.le_refl _
                refine Run.le_bind (ihE m st recv k hk) fun st r => ?_
                cases r <;>
                  first
                  | exact Run.le_refl _
                  | exact ihAttrC m st _ attr cargs.toList k hk
                  | skip
                case ntuple tn fs xs =>
                  -- iota-reduce the receiver matcher, then fork on the plan
                  dsimp only
                  cases ntupleCallPlan m tn fs attr <;> try exact Run.le_refl _
                  case instMethod qname =>
                    exact Run.le_bind (ihEs m st cargs.toList k hk) fun st vs =>
                      Run.le_withLocals
                        (ihCall m st.world qname ((RVal.ntuple tn fs xs :: vs).toArray) k hk)
                case str sv =>
                  -- str METHOD dispatch (H5 strings): fork on the pure plan;
                  -- every in-tier arm is args + a fuel-independent worker
                  dsimp only
                  cases strCallPlan attr <;>
                    first
                    | exact Run.le_refl _
                    | exact Run.le_bind (ihEs m st cargs.toList k hk)
                        fun st vs => Run.le_refl _
              case name fname _ =>
                dsimp only
                cases Env.lookup st.locals fname with
                | some v =>
                  cases v <;>
                    first
                    | exact Run.le_refl _
                    | exact Run.le_bind (ihEs m st cargs.toList k hk) fun _ _ =>
                        Run.le_refl _
                    | skip
                  case ref a =>
                    -- H7: the guarded closure call
                    refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                    refine Run.le_ite (Run.le_refl _) ?_
                    cases Heap.get? st.world.heap a with
                    | none => exact Run.le_refl _
                    | some o =>
                      cases o <;> try exact Run.le_refl _
                      case closure nm ps ao lo hg ig bd cap =>
                        exact Run.le_bind (Run.le_refl _) fun st cap' =>
                          Run.le_withLocals
                            (ihClosure m st.world
                              nm ps ao lo ig bd cap' vs.toArray k hk)
                | none =>
                  -- module globals (G1) → module function → builtins →
                  -- NameError/unsupported (the globals and the final fork are
                  -- fuel-independent, hence `le_refl`)
                  cases lookupG (moduleGlobals m).1 fname with
                  | some vv =>
                    cases vv with
                    | some v =>
                      cases v <;>
                        exact Run.le_bind (ihEs m st cargs.toList k hk) fun _ _ =>
                          Run.le_refl _
                    | none =>
                      -- pass 3: the poisoned-arm live view — value/exn
                      -- arms bind then decide; a closure ref recurses
                      -- through `callClosure` (its own conjunct)
                      cases Env.lookup st.world.globals fname with
                      | none => exact Run.le_refl _
                      | some v =>
                        cases v <;>
                          first
                            | exact Run.le_bind (ihEs m st cargs.toList k hk)
                                fun st _ => Run.le_refl _
                            | skip
                        case ref a =>
                          refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                          refine Run.le_ite (Run.le_refl _) ?_
                          cases Heap.get? st.world.heap a with
                          | none => exact Run.le_refl _
                          | some obj =>
                            cases obj <;> try exact Run.le_refl _
                            case closure nm ps ao lo hg ig bd cap =>
                              exact Run.le_bind (Run.le_refl _) fun st cap' =>
                                Run.le_withLocals
                                  (ihClosure m st.world
                                    nm ps ao lo ig bd cap' vs.toArray k hk)
                  | none =>
                    -- findFunction (def/class collision → call) → class
                    -- instantiation (guards, args, `__init__` through
                    -- `callIn`) → len → sorted → max → min → abs → int →
                    -- NameError/unsupported (each builtin: bind args, result
                    -- fuel-independent)
                    have hb : ∀ {β : Type} (g : FrameState → List RVal → Run FrameState β),
                        (evalExprs m fuel st cargs.toList).bind g ⊑ʳ
                        (evalExprs m k st cargs.toList).bind g :=
                      fun g => Run.le_bind (ihEs m st cargs.toList k hk)
                        fun st vs => Run.le_refl _
                    refine Run.le_ite
                      (Run.le_ite (Run.le_refl _)
                        (Run.le_bind (ihEs m st cargs.toList k hk) fun st vs =>
                          Run.le_withLocals (ihCall m st.world fname vs.toArray k hk)))
                      ?_
                    cases findClass m fname with
                    | some p =>
                      obtain ⟨ci, c⟩ := p
                      -- namedtuple-collision guard, then the exceptions
                      -- tier's isExc guard (both fuel-independent)
                      refine Run.le_ite (Run.le_refl _) (Run.le_ite (Run.le_refl _) ?_)
                      cases c.ntBase with
                      | some nt =>
                        -- value-like subclass construction (H5): guards,
                        -- then args, then a fuel-independent value/arity fork
                        refine Run.le_ite (Run.le_refl _) (Run.le_ite (Run.le_refl _)
                          (Run.le_ite (Run.le_refl _) ?_))
                        exact Run.le_bind (ihEs m st cargs.toList k hk)
                          fun st vs => Run.le_refl _
                      | none =>
                        refine Run.le_ite (Run.le_refl _) (Run.le_ite (Run.le_refl _) ?_)
                        refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                        refine Run.le_ite ?_ (Run.le_refl _)
                        refine Run.le_bind (Run.le_withLocals
                          (ihCall m _ (fname ++ ".__init__") ((RVal.ref st.world.heap.size :: vs).toArray) k hk))
                          fun st'' r => ?_
                        cases r <;> exact Run.le_refl _
                    | none =>
                      -- namedtuple construction binds the arguments, then a
                      -- fuel-independent value/arity fork; the builtin chain
                      -- is as before
                      cases findNamedTuple m fname with
                      | some nt => exact hb _
                      | none =>
                        -- len, sorted (drains a generator), max/min (the
                        -- guarded drain), any/all (the short-circuit
                        -- drain), abs, int, enumerate, count (both
                        -- ALLOCATE an iterator object), NEXT (binds the
                        -- args, then steps the generator), ord, chr
                        -- len → sorted → max → min → any/all → set → abs →
                        -- int → sum → tuple → list → dict → range →
                        -- enumerate → count → next → ord → chr → tail
                        refine Run.le_ite (hb _)                             -- len
                            (Run.le_ite ?_                                     -- sorted
                             (Run.le_ite ?_                                    -- max
                              (Run.le_ite ?_                                   -- min
                               (Run.le_ite ?_                                  -- any/all
                                (Run.le_ite ?_                                 -- set
                                 (Run.le_ite (hb _)                            -- abs
                                  (Run.le_ite (hb _)                           -- int
                                   (Run.le_ite ?_                              -- sum
                                    (Run.le_ite ?_                             -- tuple
                                     (Run.le_ite ?_                            -- list
                                      (Run.le_ite (hb _)                       -- dict
                                       (Run.le_ite (hb _)                      -- range
                                      (Run.le_ite (hb _)                       -- enumerate
                                       (Run.le_ite (hb _)                      -- count
                                        (Run.le_ite ?_                         -- next
                                         (Run.le_ite (hb _)                    -- ord
                                            (Run.le_ite (hb _)                 -- chr
                                             ?_)))))))))))))))))
                        -- sorted
                        · refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                          cases vs with
                          | nil => exact Run.le_refl _
                          | cons v vtail =>
                            cases vtail with
                            | cons _ _ => exact Run.le_refl _
                            | nil =>
                              dsimp only
                              cases v <;> try exact Run.le_refl _
                              case ref a =>
                                dsimp only
                                cases Heap.get? st.world.heap a with
                                | none => exact Run.le_refl _
                                | some obj =>
                                  cases obj <;> try exact Run.le_refl _
                                  case generator q l c stat =>
                                    refine Run.le_bind
                                      (Run.le_withLocals (ihDrain m st.world a k hk))
                                      fun st vals => ?_
                                    exact Run.le_bind (Run.le_refl _) fun st s2 =>
                                      Run.le_refl _
                        -- max
                        · refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                          cases vs with
                          | nil => exact Run.le_refl _
                          | cons v vtail =>
                            cases v <;> try exact Run.le_refl _
                            case ref a =>
                              cases vtail with
                              | cons _ _ => exact Run.le_refl _
                              | nil =>
                                dsimp only
                                cases Heap.get? st.world.heap a with
                                | none => exact Run.le_refl _
                                | some obj =>
                                  cases obj <;> try exact Run.le_refl _
                                  case generator q l c stat =>
                                    refine Run.le_ite (Run.le_refl _) ?_
                                    refine Run.le_bind
                                      (Run.le_withLocals (ihDrain m st.world a k hk))
                                      fun st vals => ?_
                                    exact Run.le_refl _
                        -- min
                        · refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                          cases vs with
                          | nil => exact Run.le_refl _
                          | cons v vtail =>
                            cases v <;> try exact Run.le_refl _
                            case ref a =>
                              cases vtail with
                              | cons _ _ => exact Run.le_refl _
                              | nil =>
                                dsimp only
                                cases Heap.get? st.world.heap a with
                                | none => exact Run.le_refl _
                                | some obj =>
                                  cases obj <;> try exact Run.le_refl _
                                  case generator q l c stat =>
                                    refine Run.le_ite (Run.le_refl _) ?_
                                    refine Run.le_bind
                                      (Run.le_withLocals (ihDrain m st.world a k hk))
                                      fun st vals => ?_
                                    exact Run.le_refl _
                        -- any/all
                        · refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                          cases vs with
                          | nil => exact Run.le_refl _
                          | cons v vtail =>
                            cases vtail with
                            | cons _ _ => exact Run.le_refl _
                            | nil =>
                              cases v <;> try exact Run.le_refl _
                              case ref a =>
                                dsimp only
                                cases Heap.get? st.world.heap a with
                                | none => exact Run.le_refl _
                                | some obj =>
                                  cases obj <;> try exact Run.le_refl _
                                  case generator q l c stat =>
                                    refine Run.le_bind
                                      (Run.le_withLocals
                                        (ihAnyAll m st.world a (fname == "all") k hk))
                                      fun st b => ?_
                                    exact Run.le_refl _
                        -- set (H7+): binds, then per-receiver dedup
                        -- (fuel-threaded scans) or the generator drain
                        · refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                          cases vs with
                          | nil => exact Run.le_refl _
                          | cons v vtail =>
                            cases vtail with
                            | cons _ _ => exact Run.le_refl _
                            | nil =>
                              dsimp only
                              cases v <;>
                                first
                                | exact Run.le_refl _
                                | exact Run.le_bind (Run.le_liftRes (setDedup_mono hk _))
                                    fun st es => Run.le_refl _
                                | skip
                              case rangeV lo hi step =>
                                exact Run.le_bind (Run.le_refl _) fun st xs =>
                                  Run.le_bind (Run.le_liftRes (setDedup_mono hk _))
                                    fun st es => Run.le_refl _
                              case ref a =>
                                dsimp only
                                cases Heap.get? st.world.heap a with
                                | none => exact Run.le_refl _
                                | some obj =>
                                  cases obj <;>
                                    first
                                    | exact Run.le_refl _
                                    | exact Run.le_bind (Run.le_liftRes (setDedup_mono hk _))
                                        fun st es => Run.le_refl _
                                    | skip
                                  case generator q l c stat =>
                                    refine Run.le_bind
                                      (Run.le_withLocals (ihDrain m st.world a k hk))
                                      fun st vals => ?_
                                    exact Run.le_bind (Run.le_liftRes (setDedup_mono hk _))
                                      fun st es => Run.le_refl _
                        -- sum (pass 3): arity fork, the str-start fork,
                        -- then the receiver — every value arm is the pure
                        -- fold; the single-generator arm drains behind the
                        -- `moduleGenFree` guard, like max/min
                        · refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                          cases sumArgs vs with
                          | none => exact Run.le_refl _
                          | some pr =>
                            obtain ⟨v, start⟩ := pr
                            dsimp only
                            cases start <;> try exact Run.le_refl _
                            all_goals
                              cases v <;> try exact Run.le_refl _
                            all_goals
                              case ref a =>
                                dsimp only
                                cases Heap.get? st.world.heap a with
                                | none => exact Run.le_refl _
                                | some obj =>
                                  cases obj <;> try exact Run.le_refl _
                                  case generator q l c stat =>
                                    refine Run.le_ite (Run.le_refl _) ?_
                                    exact Run.le_bind
                                      (Run.le_withLocals (ihDrain m st.world a k hk))
                                      fun st vals => Run.le_refl _
                        -- tuple (pass 3): snapshot constructors are
                        -- fuel-free; the generator arm drains, guarded
                        · refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                          cases vs with
                          | nil => exact Run.le_refl _
                          | cons v vtail =>
                            cases vtail with
                            | cons _ _ => exact Run.le_refl _
                            | nil =>
                              dsimp only
                              cases v <;> try exact Run.le_refl _
                              case ref a =>
                                dsimp only
                                cases Heap.get? st.world.heap a with
                                | none => exact Run.le_refl _
                                | some obj =>
                                  cases obj <;> try exact Run.le_refl _
                                  case generator q l c stat =>
                                    refine Run.le_ite (Run.le_refl _) ?_
                                    exact Run.le_bind
                                      (Run.le_withLocals (ihDrain m st.world a k hk))
                                      fun st vals => Run.le_refl _
                        -- list (2026-08-13): `tuple`'s inventory with an
                        -- allocation, and the generator arm drains
                        -- UNGUARDED (the call is outside heapFree, so no
                        -- `moduleGenFree` ite to walk)
                        · refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                          cases vs with
                          | nil => exact Run.le_refl _
                          | cons v vtail =>
                            cases vtail with
                            | cons _ _ => exact Run.le_refl _
                            | nil =>
                              dsimp only
                              cases v <;> try exact Run.le_refl _
                              case ref a =>
                                dsimp only
                                cases Heap.get? st.world.heap a with
                                | none => exact Run.le_refl _
                                | some obj =>
                                  cases obj <;> try exact Run.le_refl _
                                  case generator q l c stat =>
                                    exact Run.le_bind
                                      (Run.le_withLocals (ihDrain m st.world a k hk))
                                      fun st vals => Run.le_refl _
                        -- next
                        · refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                          cases vs with
                          | nil => exact Run.le_refl _
                          | cons v rest =>
                            cases v <;> try exact Run.le_refl _
                            case ref ad =>
                              cases rest with
                              | nil =>
                                refine Run.le_bind
                                  (Run.le_withLocals (ihStep m st.world ad k hk))
                                  fun st r => ?_
                                cases r <;> exact Run.le_refl _
                              | cons d rest' =>
                                cases rest' with
                                | nil =>
                                  refine Run.le_bind
                                    (Run.le_withLocals (ihStep m st.world ad k hk))
                                    fun st r => ?_
                                  cases r <;> exact Run.le_refl _
                                | cons _ _ => exact Run.le_refl _
                        -- the tail: str (pass 8 — args bind, pure
                        -- worker) / input / print / module dunder, then
                        -- the pass-3 absent-arm live view — the closure
                        -- dispatch recurses through callClosure
                        · refine Run.le_ite
                            (Run.le_bind (ihEs m st cargs.toList k hk)
                              fun st _ => Run.le_refl _)
                            (Run.le_ite (Run.le_refl _)
                              (Run.le_ite
                                (Run.le_bind (ihEs m st cargs.toList k hk)
                                  fun st _ => Run.le_refl _)
                                (Run.le_ite (Run.le_refl _) ?_)))
                          cases Env.lookup st.world.globals fname with
                          | none => exact Run.le_refl _
                          | some v =>
                            cases v <;>
                              first
                                | exact Run.le_bind (ihEs m st cargs.toList k hk)
                                    fun st _ => Run.le_refl _
                                | skip
                            case ref a =>
                              refine Run.le_bind (ihEs m st cargs.toList k hk) fun st vs => ?_
                              refine Run.le_ite (Run.le_refl _) ?_
                              cases Heap.get? st.world.heap a with
                              | none => exact Run.le_refl _
                              | some obj =>
                                cases obj <;> try exact Run.le_refl _
                                case closure nm ps ao lo hg ig bd cap =>
                                  exact Run.le_bind (Run.le_refl _) fun st cap' =>
                                    Run.le_withLocals
                                      (ihClosure m st.world
                                        nm ps ao lo ig bd cap' vs.toArray k hk)
        | genExp elt tgt it ifs wb _ =>
          simp only [evalExpr]; exact Run.le_refl _
        | list elts _ =>
          simp only [evalExpr]
          exact Run.le_bind (ihEs m st elts.toList k hk) fun st vs => Run.le_refl _
        | tuple elts _ =>
          simp only [evalExpr]
          exact Run.le_bind (ihEs m st elts.toList k hk) fun st vs => Run.le_refl _
        | subscript v idx _ =>
          simp only [evalExpr]
          exact Run.le_bind (ihE m st v k hk) fun st c =>
            Run.le_bind (ihE m st idx k hk) fun st i => Run.le_refl _
        | dict keys values _ =>
          simp only [evalExpr]
          exact Run.le_bind (ihItems m st keys.toList values.toList k hk)
            fun st items => Run.le_bind (Run.le_refl _) fun st entries =>
              Run.le_refl _
        | «attribute» recv attr _ =>
          -- attribute READ (H3): receiver, then a fuel-free heap fork
          simp only [evalExpr]
          exact Run.le_bind (ihE m st recv k hk) fun st r => Run.le_refl _
        | ifExp t b o _ =>
          simp only [evalExpr]
          exact Run.le_bind (ihE m st t k hk) fun st tv =>
            Run.le_bind (Run.le_refl _) fun st cond =>
              Run.le_ite (ihE m st b k hk) (ihE m st o k hk)
        | slice v l u stp _ =>
          -- H5 strings: four sequential component binds, then the pure
          -- (fuel-independent) `sliceVal`
          simp only [evalExpr]
          exact Run.le_bind (ihE m st v k hk) fun st cv =>
            Run.le_bind (ihE m st l k hk) fun st lv =>
              Run.le_bind (ihE m st u k hk) fun st uv =>
                Run.le_bind (ihE m st stp k hk) fun st sv => Run.le_refl _
        | unsupported pyKind text _ => simp only [evalExpr]; exact Run.le_refl _
    -- evalExprs
    · intro m st es fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases es with
        | nil => simp only [evalExprs]; exact Run.le_refl _
        | cons e rest =>
          simp only [evalExprs]
          exact Run.le_bind (ihE m st e k hk) fun st v =>
            Run.le_bind (ihEs m st rest k hk) fun st vs => Run.le_refl _
    -- evalBoolChain
    · intro m st op e rest fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        simp only [evalBoolChain]
        refine Run.le_bind (ihE m st e k hk) fun st v => ?_
        cases rest with
        | nil => exact Run.le_refl _
        | cons e' rest' =>
          refine Run.le_bind (Run.le_refl _) fun st b => ?_
          cases op with
          | and => exact Run.le_ite (ihB m st .and e' rest' k hk) (Run.le_refl _)
          | or => exact Run.le_ite (Run.le_refl _) (ihB m st .or e' rest' k hk)
    -- evalCompareChain
    · intro m st lhs ops cs fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases ops with
        | nil =>
          cases cs with
          | nil => simp only [evalCompareChain]; exact Run.le_refl _
          | cons c cs' => simp only [evalCompareChain]; exact Run.le_refl _
        | cons op ops' =>
          cases cs with
          | nil => simp only [evalCompareChain]; exact Run.le_refl _
          | cons e rest =>
            simp only [evalCompareChain]
            exact Run.le_bind (ihE m st e k hk) fun st rhs =>
              Run.le_bind (Run.le_liftRes (evalCompareOpH_mono hk)) fun st b =>
                Run.le_ite (ihC m st rhs ops' rest k hk) (Run.le_refl _)
    -- execStmt
    · intro m st s fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases s with
        | defStmt name params ao lo hg ig body caps _ =>
          simp only [execStmt]; exact Run.le_refl _
        | yieldFromStmt v _ =>
          -- pass 5: an un-lowered `yield from` refuses, fuel-free
          simp only [execStmt]; exact Run.le_refl _
        | raiseStmt exc cause _ =>
          -- fuel-free: the raise arm only does pure lookups
          simp only [execStmt]; exact Run.le_refl _
        | delStmt names _ =>
          -- del RECONCILED: fuel-free — a pure fold over the locals
          simp only [execStmt]; exact Run.le_refl _
        | assertStmt test msg _ =>
          -- the tail batch: two evalExpr calls, the message's only on
          -- the FAILING branch — an ordinary bind-shaped arm
          simp only [execStmt]
          refine Run.le_bind (ihE m st test k hk) fun st t => ?_
          refine Run.le_bind (Run.le_refl _) fun st b => ?_
          refine Run.le_ite (Run.le_refl _) ?_
          cases msg with
          | none => exact Run.le_refl _
          | some e =>
            exact Run.le_bind (ihE m st e k hk) fun st v => Run.le_refl _
        | tryStmt body excName handler tu _ =>
          simp only [execStmt]
          cases tu with
          | some reason => exact Run.le_refl _
          | none =>
            -- shadow guard, handler-class resolution, isExc — all
            -- fuel-independent; then the body run (IH), the match on its
            -- retained outcome, and the handler run (IH again)
            refine Run.le_ite (Run.le_refl _) ?_
            cases findClass m excName with
            | none =>
              -- Pass 0 (§import forms): the pinned import-error table
              -- branch — the class branch's body/handler IH shape, with
              -- no cid ite (every `.importError` matches either name)
              refine Run.le_ite ?_ (Run.le_refl _)
              rcases ihSs m st body.toList k hk with h | h
              · rw [h]; exact Or.inl rfl
              · rw [h]
                cases execStmts m k st body.toList with
                | ok st' flow => exact Run.le_refl _
                | exn st' e =>
                  cases e <;> try exact Run.le_refl _
                  case importError mod =>
                    exact ihSs m st' handler.toList k hk
                | timeout => exact Run.le_refl _
                | unsupported msg => exact Run.le_refl _
            | some p =>
              obtain ⟨ci, c⟩ := p
              refine Run.le_ite (Run.le_refl _) ?_
              rcases ihSs m st body.toList k hk with h | h
              · rw [h]; exact Or.inl rfl
              · rw [h]
                cases execStmts m k st body.toList with
                | ok st' flow => exact Run.le_refl _
                | exn st' e =>
                  cases e <;> try exact Run.le_refl _
                  case user cid nm =>
                    exact Run.le_ite (ihSs m st' handler.toList k hk)
                      (Run.le_refl _)
                | timeout => exact Run.le_refl _
                | unsupported msg => exact Run.le_refl _
        | importFrom mod names star _ =>
          -- Pass 0 (§import forms): fuel-free — the arm raises
          -- immediately, state unchanged (the raiseStmt shape)
          simp only [execStmt]; exact Run.le_refl _
        | ret value _ =>
          cases value with
          | none => simp only [execStmt]; exact Run.le_refl _
          | some e =>
            simp only [execStmt]
            exact Run.le_bind (ihE m st e k hk) fun st v => Run.le_refl _
        | assign targets value _ =>
          simp only [execStmt]
          cases targets.toList with
          | nil => exact Run.le_refl _
          | cons t rest =>
            cases rest with
            | nil =>
              -- subscript targets: value, primary, key, then the
              -- fuel-independent store; every other target: the old shape
              cases t
              case subscript dE kE sp =>
                exact Run.le_bind (ihE m st value k hk) fun st v =>
                  Run.le_bind (ihE m st dE k hk) fun st c =>
                    Run.le_bind (ihE m st kE k hk) fun st kk => Run.le_refl _
              case «attribute» recvE attr sp =>
                exact Run.le_bind (ihE m st value k hk) fun st v =>
                  Run.le_bind (ihE m st recvE k hk) fun st r => Run.le_refl _
              case tuple elts sp =>
                -- pass 4: the all-names/attribute-elements fork — both
                -- branches bind the value, then a fuel-free tail
                exact Run.le_ite
                  (Run.le_bind (ihE m st value k hk) fun st v => Run.le_refl _)
                  (Run.le_bind (ihE m st value k hk) fun st v => Run.le_refl _)
              all_goals
                exact Run.le_bind (ihE m st value k hk) fun st v =>
                  Run.le_bind (Run.le_refl _) fun st env' => Run.le_refl _
            | cons t2 rest2 =>
              -- the compiled matcher still splits on the head constructor
              cases t <;> exact Run.le_refl _
        | augAssign target op value _ =>
          cases target <;> try (simp only [execStmt]; exact Run.le_refl _)
          case name id _ =>
            simp only [execStmt]
            cases Env.lookup st.locals id with
            | none => exact Run.le_refl _
            | some old =>
              cases old <;>
                first
                | exact Run.le_refl _
                | exact Run.le_bind (ihE m st value k hk) fun st v =>
                    Run.le_bind (Run.le_refl _) fun st r => Run.le_refl _
          case «attribute» recvE attr _ =>
            -- pass 4: receiver, the fuel-free attribute load, then (for
            -- immediate old values) the value and the fuel-free store
            simp only [execStmt]
            refine Run.le_bind (ihE m st recvE k hk) fun st r => ?_
            cases r <;> try exact Run.le_refl _
            case ref a =>
              refine Run.le_bind (Run.le_refl _) fun st old => ?_
              cases old <;>
                first
                | exact Run.le_refl _
                | exact Run.le_bind (ihE m st value k hk) fun st v =>
                    Run.le_bind (Run.le_refl _) fun st res =>
                      Run.le_bind (Run.le_refl _) fun st h' => Run.le_refl _
        | whileLoop test body orelse _ =>
          simp only [execStmt]
          exact ihW m st test body.toList orelse.toList k hk
        | forStmt target iter body orelse _ =>
          simp only [execStmt]
          cases horelse : orelse.toList with
          | cons o os => exact Run.le_refl _
          | nil =>
            refine Run.le_bind (ihE m st iter k hk) fun st it => ?_
            cases it <;> try exact Run.le_refl _
            case str s =>
              exact ihFor m st target (strCharVals s) body.toList k hk
            case listV xs => exact ihFor m st target xs.toList body.toList k hk
            case tuple xs => exact ihFor m st target xs.toList body.toList k hk
            case ntuple tn fs xs => exact ihFor m st target xs.toList body.toList k hk
            case rangeV lo hi step =>
              exact Run.le_bind (Run.le_refl _) fun st xs =>
                ihFor m st target xs body.toList k hk
            case ref a => exact ihForL m st target a 0 body.toList k hk
        | ifStmt test body orelse _ =>
          simp only [execStmt]
          exact Run.le_bind (ihE m st test k hk) fun st t =>
            Run.le_bind (Run.le_refl _) fun st b =>
              Run.le_ite (ihSs m st body.toList k hk) (ihSs m st orelse.toList k hk)
        | exprStmt e _ =>
          simp only [execStmt]
          exact Run.le_bind (ihE m st e k hk) fun st v => Run.le_refl _
        | yieldStmt e _ => simp only [execStmt]; exact Run.le_refl _
        | pass _ => simp only [execStmt]; exact Run.le_refl _
        | brk _ => simp only [execStmt]; exact Run.le_refl _
        | cont _ => simp only [execStmt]; exact Run.le_refl _
        | unsupported pyKind text _ => simp only [execStmt]; exact Run.le_refl _
    -- execStmts
    · intro m st ss fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases ss with
        | nil => simp only [execStmts]; exact Run.le_refl _
        | cons s rest =>
          simp only [execStmts]
          refine Run.le_bind (ihS m st s k hk) fun st flow => ?_
          cases flow with
          | next => exact ihSs m st rest k hk
          | ret v => exact Run.le_refl _
          | brk => exact Run.le_refl _
          | cont => exact Run.le_refl _
    -- execWhile
    · intro m st test body orelse fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        simp only [execWhile]
        refine Run.le_bind (ihE m st test k hk) fun st t => ?_
        refine Run.le_bind (Run.le_refl _) fun st b => ?_
        refine Run.le_ite ?_ (ihSs m st orelse k hk)
        refine Run.le_bind (ihSs m st body k hk) fun st flow => ?_
        cases flow with
        | next => exact ihW m st test body orelse k hk
        | ret v => exact Run.le_refl _
        | brk => exact Run.le_refl _
        | cont => exact ihW m st test body orelse k hk
    -- callIn
    · intro m w fname args fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        simp only [callIn]
        cases findFunction m fname with
        | none => exact Run.le_refl _
        | some f =>
          -- argsOk / localsOk / arity guards, then the H4 generator
          -- branch (allocation only — fuel-independent)
          refine Run.le_ite (Run.le_refl _) (Run.le_ite (Run.le_refl _)
            (Run.le_ite (Run.le_refl _) (Run.le_ite (Run.le_refl _) ?_)))
          refine Run.le_toWorld
            (Run.le_bind (ihSs m ⟨w, mkCallEnv f.params args⟩ f.body.toList k hk)
              fun st flow => ?_)
          cases flow <;> exact Run.le_refl _
    -- execFor
    · intro m st target xs body fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases xs with
        | nil => simp only [execFor]; exact Run.le_refl _
        | cons x rest =>
          simp only [execFor]
          refine Run.le_bind (Run.le_refl _) fun st env₁ => ?_
          refine Run.le_bind (ihSs m { st with locals := env₁ } body k hk)
            fun st flow => ?_
          cases flow with
          | next => exact ihFor m st target rest body k hk
          | cont => exact ihFor m st target rest body k hk
          | brk => exact Run.le_refl _
          | ret v => exact Run.le_refl _
    -- evalDictItems
    · intro m st keys values fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases keys with
        | nil => cases values <;> (simp only [evalDictItems]; exact Run.le_refl _)
        | cons kE ks =>
          cases values with
          | nil => simp only [evalDictItems]; exact Run.le_refl _
          | cons vE vs =>
            simp only [evalDictItems]
            exact Run.le_bind (ihE m st kE k hk) fun st kv =>
              Run.le_bind (ihE m st vE k hk) fun st vv =>
                Run.le_bind (ihItems m st ks vs k hk) fun st rest' =>
                  Run.le_refl _
    -- execForList (H2: the live list cursor)
    · intro m st target a i body fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        simp only [execForList]
        cases Heap.get? st.world.heap a with
        | none => exact Run.le_refl _
        | some o =>
          cases o with
          | dict es ver => exact Run.le_refl _
          | «instance» ci attrs => exact Run.le_refl _
          | cell cv => exact Run.le_refl _
          | closure nm ps ao lo' hg ig bd cap => exact Run.le_refl _
          | pyset zs => exact Run.le_refl _
          | generator qn lo kk stt =>
            exact Run.le_ite (Run.le_refl _) (ihForG m st target a body k hk)
          | list xs =>
            refine Run.le_ite ?_ (Run.le_refl _)
            refine Run.le_bind (Run.le_refl _) fun st env₁ => ?_
            refine Run.le_bind (ihSs m { st with locals := env₁ } body k hk)
              fun st flow => ?_
            cases flow with
            | next => exact ihForL m st target a (i + 1) body k hk
            | cont => exact ihForL m st target a (i + 1) body k hk
            | brk => exact Run.le_refl _
            | ret v => exact Run.le_refl _
    -- execAttrCall (H3: the attribute-call dispatch)
    · intro m st a attr args fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        simp only [execAttrCall]
        cases attrCallPlan m st.world.heap a attr with
        | instMethod qname =>
          exact Run.le_bind (ihEs m st args k hk) fun st vs =>
            Run.le_withLocals
              (ihCall m st.world qname ((RVal.ref a :: vs).toArray) k hk)
        | instAttrValue => exact Run.le_refl _
        | attrMissing => exact Run.le_refl _
        | dictGet =>
          exact Run.le_bind (ihEs m st args k hk) fun st vs => Run.le_refl _
        | dictClear =>
          -- pass 5: arg-eval then a fuel-free heap update
          exact Run.le_bind (ihEs m st args k hk) fun st vs => Run.le_refl _
        | listAppend =>
          exact Run.le_bind (ihEs m st args k hk) fun st vs => Run.le_refl _
        | listPop =>
          exact Run.le_bind (ihEs m st args k hk) fun st vs => Run.le_refl _
        | listInsert =>
          -- the §2.5 residue: arg-eval then a fuel-free clamped update
          exact Run.le_bind (ihEs m st args k hk) fun st vs => Run.le_refl _
        | refuse msg => exact Run.le_refl _
        | dangling => exact Run.le_refl _
    -- stepIter (H4: the generator stepper)
    · intro m w a fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        simp only [stepIter]
        cases Heap.get? w.heap a with
        | none => exact Run.le_refl _
        | some o =>
          cases o with
          | dict es ver => exact Run.le_refl _
          | list xs => exact Run.le_refl _
          | «instance» ci attrs => exact Run.le_refl _
          | cell cv => exact Run.le_refl _
          | closure nm ps ao lo' hg ig bd cap => exact Run.le_refl _
          | pyset zs => exact Run.le_refl _
          | generator qn lo kk stt =>
            cases stt with
            | closed => exact Run.le_refl _
            | running => exact Run.le_refl _
            | created =>
              dsimp only
              cases Heap.update w.heap a (.generator qn lo kk .running) with
              | none => exact Run.le_refl _
              | some h₁ =>
                refine Run.le_toWorld (Run.le_bindE
                  (ihGen m ⟨{ w with heap := h₁ }, lo⟩ kk k hk)
                  (fun st r => ?_)
                  (fun st e => ?_))
                · cases r with
                  | none =>
                    dsimp only
                    cases Heap.update st.world.heap a
                        (.generator qn st.locals [] .closed) <;> exact Run.le_refl _
                  | some p =>
                    obtain ⟨v, cont'⟩ := p
                    dsimp only
                    cases Heap.update st.world.heap a
                        (.generator qn st.locals cont' .suspended) <;> exact Run.le_refl _
                · -- the exceptions tier's close-on-exn arm: fuel-free
                  cases Heap.update st.world.heap a
                      (.generator qn st.locals [] .closed) <;> exact Run.le_refl _
            | suspended =>
              dsimp only
              cases Heap.update w.heap a (.generator qn lo kk .running) with
              | none => exact Run.le_refl _
              | some h₁ =>
                refine Run.le_toWorld (Run.le_bindE
                  (ihGen m ⟨{ w with heap := h₁ }, lo⟩ kk k hk)
                  (fun st r => ?_)
                  (fun st e => ?_))
                · cases r with
                  | none =>
                    dsimp only
                    cases Heap.update st.world.heap a
                        (.generator qn st.locals [] .closed) <;> exact Run.le_refl _
                  | some p =>
                    obtain ⟨v, cont'⟩ := p
                    dsimp only
                    cases Heap.update st.world.heap a
                        (.generator qn st.locals cont' .suspended) <;> exact Run.le_refl _
                · -- the exceptions tier's close-on-exn arm: fuel-free
                  cases Heap.update st.world.heap a
                      (.generator qn st.locals [] .closed) <;> exact Run.le_refl _
    -- execGen (H4: the continuation walker)
    · intro m st k fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ kf =>
        have hk : fuel ≤ kf := Nat.le_of_succ_le_succ hf
        -- `execGen` pattern-matches on the CONTINUATION as well as on
        -- fuel, so its equations only fire once the frame is concrete:
        -- case first, unfold per leaf.
        cases k with
        | nil => simp only [execGen]; exact Run.le_refl _
        | cons fr rest =>
          cases fr with
          | block ss =>
            cases ss with
            | nil => simp only [execGen]; exact ihGen m st rest kf hk
            | cons s ss' =>
              simp only [execGen]
              -- the H3 free-scrutinee discipline: fork on the PURE plan
              cases genPlan s with
              | delegate =>
                refine Run.le_bind (ihS m st s kf hk) fun st flow => ?_
                cases flow with
                | next => exact ihGen m st (.block ss' :: rest) kf hk
                | ret v => cases v <;> exact Run.le_refl _
                | brk =>
                  cases genBreak rest with
                  | none => exact Run.le_refl _
                  | some k'' => exact ihGen m st k'' kf hk
                | cont =>
                  cases genContinue rest with
                  | none => exact Run.le_refl _
                  | some k'' => exact ihGen m st k'' kf hk
              | yieldHere e =>
                exact Run.le_bind (ihE m st e kf hk) fun st v => Run.le_refl _
              | branch test body orelse =>
                refine Run.le_bind (ihE m st test kf hk) fun st t => ?_
                refine Run.le_bind (Run.le_refl _) fun st b => ?_
                exact ihGen m st _ kf hk
              | whileHere test body orelse => exact ihGen m st _ kf hk
              | forHere target iter body =>
                refine Run.le_bind (ihE m st iter kf hk) fun st it => ?_
                cases it with
                | none => exact Run.le_refl _
                | bool b => exact Run.le_refl _
                | int n => exact Run.le_refl _
                | str sv => exact ihGen m st _ kf hk
                | listV xs => exact ihGen m st _ kf hk
                | tuple xs => exact ihGen m st _ kf hk
                | ntuple tn fs xs => exact ihGen m st _ kf hk
                | rangeV lo hi step =>
                  exact Run.le_bind (Run.le_refl _) fun st xs => ihGen m st _ kf hk
                | ref ad =>
                  dsimp only
                  cases Heap.get? st.world.heap ad with
                  | none => exact Run.le_refl _
                  | some o =>
                    cases o with
                    | dict es ver => exact Run.le_refl _
                    | «instance» ci attrs => exact Run.le_refl _
                    | cell cv => exact Run.le_refl _
                    | closure nm ps ao lo' hg ig bd cap => exact Run.le_refl _
                    | pyset zs => exact Run.le_refl _
                    | list xs => exact ihGen m st _ kf hk
                    | generator qn lo kk stt => exact ihGen m st _ kf hk
              | refuse msg => exact Run.le_refl _
          | forSeq target xs body =>
            cases xs with
            | nil => simp only [execGen]; exact ihGen m st rest kf hk
            | cons x rest' =>
              simp only [execGen]
              refine Run.le_bind (Run.le_refl _) fun st env₁ => ?_
              exact ihGen m { st with locals := env₁ } _ kf hk
          | forList target ad i body =>
            simp only [execGen]
            cases Heap.get? st.world.heap ad with
            | none => exact Run.le_refl _
            | some o =>
              cases o with
              | dict es ver => exact Run.le_refl _
              | «instance» ci attrs => exact Run.le_refl _
              | generator qn lo kk stt => exact Run.le_refl _
              | cell cv => exact Run.le_refl _
              | closure nm ps ao lo' hg ig bd cap => exact Run.le_refl _
              | pyset zs => exact Run.le_refl _
              | list xs =>
                refine Run.le_ite ?_ (ihGen m st rest kf hk)
                refine Run.le_bind (Run.le_refl _) fun st env₁ => ?_
                exact ihGen m { st with locals := env₁ } _ kf hk
          | forGen target ad body =>
            simp only [execGen]
            refine Run.le_bind (Run.le_withLocals (ihStep m st.world ad kf hk))
              fun st r => ?_
            cases r with
            | none => exact ihGen m st rest kf hk
            | some v =>
              refine Run.le_bind (Run.le_refl _) fun st env₁ => ?_
              exact ihGen m { st with locals := env₁ } _ kf hk
          | enumSeq i xs =>
            simp only [execGen]
            cases xs <;> first | exact ihGen m st rest kf hk | exact Run.le_refl _
          | enumList i ad cur =>
            simp only [execGen]
            cases Heap.get? st.world.heap ad with
            | none => exact Run.le_refl _
            | some o =>
              cases o with
              | list xs => exact Run.le_ite (Run.le_refl _) (ihGen m st rest kf hk)
              | dict es ver => exact Run.le_refl _
              | «instance» ci attrs => exact Run.le_refl _
              | generator qn lo kk stt => exact Run.le_refl _
              | cell cv => exact Run.le_refl _
              | closure nm ps ao lo' hg ig bd cap => exact Run.le_refl _
              | pyset zs => exact Run.le_refl _
          -- §3c-i-c: the trunk refuses to STEP `enumDict`; both fuels agree
          | enumDict i ad cur n sv => simp only [execGen]; exact Run.le_refl _
          -- §3a: the trunk's `forDict` arm refuses; both fuels agree
          | forDict tg ad i n sv kd bd => simp only [execGen]; exact Run.le_refl _
          | countFrom cur step => simp only [execGen]; exact Run.le_refl _
          | whileLoop test body orelse =>
            simp only [execGen]
            refine Run.le_bind (ihE m st test kf hk) fun st t => ?_
            refine Run.le_bind (Run.le_refl _) fun st b => ?_
            exact Run.le_ite (ihGen m st _ kf hk) (ihGen m st _ kf hk)
    -- execForGen (H4: the lazy `for` cursor)
    · intro m st target a body fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        simp only [execForGen]
        refine Run.le_bind (Run.le_withLocals (ihStep m st.world a k hk))
          fun st r => ?_
        cases r with
        | none => exact Run.le_refl _
        | some v =>
          refine Run.le_bind (Run.le_refl _) fun st env₁ => ?_
          refine Run.le_bind (ihSs m { st with locals := env₁ } body k hk)
            fun st flow => ?_
          cases flow with
          | next => exact ihForG m st target a body k hk
          | cont => exact ihForG m st target a body k hk
          | brk => exact Run.le_refl _
          | ret v => exact Run.le_refl _
    -- drainIter (H6: the full drain)
    · intro m w a fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        simp only [drainIter]
        refine Run.le_bind (ihStep m w a k hk) fun w r => ?_
        cases r with
        | none => exact Run.le_refl _
        | some v =>
          exact Run.le_bind (ihDrain m w a k hk) fun w vs => Run.le_refl _
    -- anyAllIter (H6: the short-circuit drain)
    · intro m w a isAll fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        simp only [anyAllIter]
        refine Run.le_bind (ihStep m w a k hk) fun w r => ?_
        cases r with
        | none => exact Run.le_refl _
        | some v =>
          refine Run.le_bind (Run.le_refl _) fun w b => ?_
          split
          · exact Run.le_refl _
          · exact ihAnyAll m w a isAll k hk
    -- callClosure (H7: the closure invocation)
    · intro m w name params ao lo ig body cap args fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        simp only [callClosure]
        refine Run.le_ite (Run.le_refl _) (Run.le_ite (Run.le_refl _)
          (Run.le_ite (Run.le_refl _) ?_))
        refine Run.le_ite (Run.le_refl _) ?_
        refine Run.le_toWorld ?_
        refine Run.le_bind
          (ihSs m ⟨w, mkCallEnv params args ++ cap⟩ body.toList k hk)
          fun st flow => ?_
        cases flow <;> exact Run.le_refl _

/-! ## Per-function corollaries (the `FuelMono` statement shape) -/

private theorem mono_of_le {α : Type} {x y r : Res α}
    (hle : x ⊑ y) (h : x = r) (hr : r ≠ .timeout) : y = r := by
  subst h; exact (Res.le_eq hle hr).symm

private theorem mono_of_leR {σ α : Type} {x y r : Run σ α}
    (hle : x ⊑ʳ y) (h : x = r) (hr : r ≠ .timeout) : y = r := by
  subst h; exact (Run.le_eq hle hr).symm

/-- Fuel monotonicity for `evalExpr`: a decided outcome (state and value)
survives any fuel increase, exactly. -/
theorem evalExpr_mono {m : Module} {fuel : Nat} {st : FrameState} {e : Expr}
    {r : Run FrameState RVal} (h : evalExpr m fuel st e = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, evalExpr m fuel' st e = r := fun fuel' hf =>
  mono_of_leR ((fuelMono fuel).1 m st e fuel' hf) h hr

/-- Fuel monotonicity for `evalExprs`. -/
theorem evalExprs_mono {m : Module} {fuel : Nat} {st : FrameState} {es : List Expr}
    {r : Run FrameState (List RVal)} (h : evalExprs m fuel st es = r)
    (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, evalExprs m fuel' st es = r := fun fuel' hf =>
  mono_of_leR ((fuelMono fuel).2.1 m st es fuel' hf) h hr

/-- Fuel monotonicity for `evalBoolChain`. -/
theorem evalBoolChain_mono {m : Module} {fuel : Nat} {st : FrameState} {op : BoolOp}
    {e : Expr} {rest : List Expr} {r : Run FrameState RVal}
    (h : evalBoolChain m fuel st op e rest = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, evalBoolChain m fuel' st op e rest = r := fun fuel' hf =>
  mono_of_leR ((fuelMono fuel).2.2.1 m st op e rest fuel' hf) h hr

/-- Fuel monotonicity for `evalCompareChain`. -/
theorem evalCompareChain_mono {m : Module} {fuel : Nat} {st : FrameState} {lhs : RVal}
    {ops : List CmpOp} {cs : List Expr} {r : Run FrameState RVal}
    (h : evalCompareChain m fuel st lhs ops cs = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, evalCompareChain m fuel' st lhs ops cs = r := fun fuel' hf =>
  mono_of_leR ((fuelMono fuel).2.2.2.1 m st lhs ops cs fuel' hf) h hr

/-- Fuel monotonicity for `execStmt`. -/
theorem execStmt_mono {m : Module} {fuel : Nat} {st : FrameState} {s : Stmt}
    {r : Run FrameState RFlow} (h : execStmt m fuel st s = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, execStmt m fuel' st s = r := fun fuel' hf =>
  mono_of_leR ((fuelMono fuel).2.2.2.2.1 m st s fuel' hf) h hr

/-- Fuel monotonicity for `execStmts`. -/
theorem execStmts_mono {m : Module} {fuel : Nat} {st : FrameState} {ss : List Stmt}
    {r : Run FrameState RFlow} (h : execStmts m fuel st ss = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, execStmts m fuel' st ss = r := fun fuel' hf =>
  mono_of_leR ((fuelMono fuel).2.2.2.2.2.1 m st ss fuel' hf) h hr

/-- Fuel monotonicity for `execWhile`. -/
theorem execWhile_mono {m : Module} {fuel : Nat} {st : FrameState} {test : Expr}
    {body orelse : List Stmt} {r : Run FrameState RFlow}
    (h : execWhile m fuel st test body orelse = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, execWhile m fuel' st test body orelse = r := fun fuel' hf =>
  mono_of_leR ((fuelMono fuel).2.2.2.2.2.2.1 m st test body orelse fuel' hf) h hr

/-- Fuel monotonicity for `callIn`: a decided nested-call outcome (world
and value) is the same at every larger fuel. -/
theorem callIn_mono {m : Module} {w : World} {fname : String} {args : Array RVal}
    {fuel : Nat} {r : Run World RVal} (h : callIn m fuel w fname args = r)
    (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, callIn m fuel' w fname args = r := fun fuel' hf =>
  mono_of_leR ((fuelMono fuel).2.2.2.2.2.2.2.1 m w fname args fuel' hf) h hr

/-- Fuel monotonicity for `execFor`. -/
theorem execFor_mono {m : Module} {fuel : Nat} {st : FrameState} {target : Expr}
    {xs : List RVal} {body : List Stmt} {r : Run FrameState RFlow}
    (h : execFor m fuel st target xs body = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, execFor m fuel' st target xs body = r := fun fuel' hf =>
  mono_of_leR ((fuelMono fuel).2.2.2.2.2.2.2.2.1 m st target xs body fuel' hf) h hr

/-- Fuel monotonicity for `evalDictItems`. -/
theorem evalDictItems_mono {m : Module} {fuel : Nat} {st : FrameState}
    {keys values : List Expr} {r : Run FrameState (List (RVal × RVal))}
    (h : evalDictItems m fuel st keys values = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, evalDictItems m fuel' st keys values = r := fun fuel' hf =>
  mono_of_leR ((fuelMono fuel).2.2.2.2.2.2.2.2.2.1 m st keys values fuel' hf) h hr

/-- Fuel monotonicity for `execForList` (H2: the live list cursor). -/
theorem execForList_mono {m : Module} {fuel : Nat} {st : FrameState}
    {target : Expr} {a : Addr} {i : Nat} {body : List Stmt}
    {r : Run FrameState RFlow}
    (h : execForList m fuel st target a i body = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, execForList m fuel' st target a i body = r := fun fuel' hf =>
  mono_of_leR ((fuelMono fuel).2.2.2.2.2.2.2.2.2.2.1 m st target a i body fuel' hf) h hr

/-- Fuel monotonicity for `execAttrCall` (H3: the attribute-call
dispatch). -/
theorem execAttrCall_mono {m : Module} {fuel : Nat} {st : FrameState}
    {a : Addr} {attr : String} {args : List Expr} {r : Run FrameState RVal}
    (h : execAttrCall m fuel st a attr args = r) (hr : r ≠ .timeout)
    (fuel' : Nat) (hf : fuel ≤ fuel') : execAttrCall m fuel' st a attr args = r :=
  mono_of_leR ((fuelMono fuel).2.2.2.2.2.2.2.2.2.2.2.1 m st a attr args fuel' hf) h hr

/-- Fuel monotonicity for `stepIter` (H4: the generator stepper). -/
theorem stepIter_mono {m : Module} {fuel : Nat} {w : World} {a : Addr}
    {r : Run World (Option RVal)} (h : stepIter m fuel w a = r)
    (hr : r ≠ .timeout) (fuel' : Nat) (hf : fuel ≤ fuel') :
    stepIter m fuel' w a = r :=
  mono_of_leR ((fuelMono fuel).2.2.2.2.2.2.2.2.2.2.2.2.1 m w a fuel' hf) h hr

/-- Fuel monotonicity for `execGen` (H4: the continuation walker). -/
theorem execGen_mono {m : Module} {fuel : Nat} {st : FrameState} {k : GenCont}
    {r : Run FrameState (Option (RVal × GenCont))} (h : execGen m fuel st k = r)
    (hr : r ≠ .timeout) (fuel' : Nat) (hf : fuel ≤ fuel') :
    execGen m fuel' st k = r :=
  mono_of_leR ((fuelMono fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.1 m st k fuel' hf) h hr

/-- Fuel monotonicity for `execForGen` (H4: the lazy `for` cursor). -/
theorem execForGen_mono {m : Module} {fuel : Nat} {st : FrameState}
    {target : Expr} {a : Addr} {body : List Stmt} {r : Run FrameState RFlow}
    (h : execForGen m fuel st target a body = r) (hr : r ≠ .timeout)
    (fuel' : Nat) (hf : fuel ≤ fuel') :
    execForGen m fuel' st target a body = r :=
  mono_of_leR ((fuelMono fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 m st target a body fuel' hf) h hr

/-- Fuel monotonicity for `drainIter` (H6: the full drain). -/
theorem drainIter_mono {m : Module} {fuel : Nat} {w : World} {a : Addr}
    {r : Run World (List RVal)}
    (h : drainIter m fuel w a = r) (hr : r ≠ .timeout)
    (fuel' : Nat) (hf : fuel ≤ fuel') :
    drainIter m fuel' w a = r :=
  mono_of_leR ((fuelMono fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 m w a fuel' hf) h hr

/-- Fuel monotonicity for `anyAllIter` (H6: the short-circuit drain). -/
theorem anyAllIter_mono {m : Module} {fuel : Nat} {w : World} {a : Addr}
    {isAll : Bool} {r : Run World Bool}
    (h : anyAllIter m fuel w a isAll = r) (hr : r ≠ .timeout)
    (fuel' : Nat) (hf : fuel ≤ fuel') :
    anyAllIter m fuel' w a isAll = r :=
  mono_of_leR ((fuelMono fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 m w a isAll fuel' hf) h hr

/-- Fuel monotonicity for `callClosure` (H7: the closure invocation). -/
theorem callClosure_mono {m : Module} {fuel : Nat} {w : World} {name : String}
    {params : Array Param} {ao lo ig : Bool} {body : Array Stmt} {cap : REnv}
    {args : Array RVal} {r : Run World RVal}
    (h : callClosure m fuel w name params ao lo ig body cap args = r)
    (hr : r ≠ .timeout) (fuel' : Nat) (hf : fuel ≤ fuel') :
    callClosure m fuel' w name params ao lo ig body cap args = r :=
  mono_of_leR ((fuelMono fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    m w name params ao lo ig body cap args fuel' hf) h hr

mutual
  /-- Fuel monotonicity of the boundary freeze: the structural arms are
  fuel-independent; the `.ref` arm is `freezeHMono`. -/
  theorem RVal.freezeB_mono (h : Heap) :
      (v : RVal) → ∀ {fuel fuel' : Nat}, fuel ≤ fuel' →
        RVal.freezeB h fuel v ⊑ RVal.freezeB h fuel' v
    | .none, _, _, _ => Res.le_refl _
    | .bool b, _, _, _ => Res.le_refl _
    | .int n, _, _, _ => Res.le_refl _
    | .str s, _, _, _ => Res.le_refl _
    | .listV xs, _, _, hf => by
        simp only [RVal.freezeB]
        exact Res.le_bind (RVal.freezeListB_mono h xs.toList hf)
          fun vs => Res.le_refl _
    | .tuple xs, _, _, hf => by
        simp only [RVal.freezeB]
        exact Res.le_bind (RVal.freezeListB_mono h xs.toList hf)
          fun vs => Res.le_refl _
    | .ntuple _ _ _, _, _, _ => Res.le_refl _
    | .rangeV .., _, _, _ => Res.le_refl _
    | .ref a, fuel, fuel', hf => (freezeHMono fuel).1 h [] (.ref a) fuel' hf

  /-- Elementwise `freezeB_mono`. -/
  theorem RVal.freezeListB_mono (h : Heap) :
      (l : List RVal) → ∀ {fuel fuel' : Nat}, fuel ≤ fuel' →
        RVal.freezeListB h fuel l ⊑ RVal.freezeListB h fuel' l
    | [], _, _, _ => Res.le_refl _
    | v :: vs, _, _, hf => by
        simp only [RVal.freezeListB]
        exact Res.le_bind (RVal.freezeB_mono h v hf) fun v' =>
          Res.le_bind (RVal.freezeListB_mono h vs hf) fun vs' => Res.le_refl _
end

/-- Fuel monotonicity of the public erasure (H2): `freezeB_mono` at the
`.ok` arm. -/
theorem Run.toPublic_mono {x : Run World RVal} {fuel fuel' : Nat}
    (hf : fuel ≤ fuel') : Run.toPublic fuel x ⊑ Run.toPublic fuel' x := by
  cases x with
  | ok w v =>
    simp only [Run.toPublic_ok]
    exact RVal.freezeB_mono w.heap v hf
  | exn w e => exact Res.le_refl _
  | timeout => exact Res.le_refl _
  | unsupported msg => exact Res.le_refl _

/-- **Public fuel monotonicity**, derived through the wrapper decomposition
(docs/memory-model.md v2): thaw and init are fuel-free, `callIn_mono`
transports the decided run, and `Run.toPublic_mono` carries the freeze
leg (fuel-free on the ref-free fast path; `freezeHMono` on returned heap
lists). -/
theorem callFunction_mono {m : Module} {fname : String} {args : Array Val}
    {fuel : Nat} {r : Res Val} (h : callFunction m fname args fuel = r)
    (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, callFunction m fname args fuel' = r := by
  intro fuel' hf
  unfold callFunction at h ⊢
  rcases (fuelMono fuel).2.2.2.2.2.2.2.1 m (initWorld m) fname
      (RVal.thawArgs args) fuel' hf with hto | heq
  · -- The inner run timed out at `fuel`: then the public result was
    -- `.timeout`, contradicting `hr`.
    rw [hto] at h
    exact absurd h.symm (by simpa using hr)
  · rw [← heq]
    have hle := Run.toPublic_mono
      (x := callIn m fuel (initWorld m) fname (RVal.thawArgs args)) hf
    rw [h] at hle
    exact (Res.le_eq hle hr).symm

/-! ## Conditional world invariance (the heap-free fragment)

Since H1-proper dict literals ALLOCATE and subscript stores MUTATE, so
unconditional world invariance is gone. What survives — and what the
pinned-state proof layer runs on — is invariance over the HEAP-FREE
fragment (`Expr.heapFree`/`Stmt.heapFree`/`Module.heapFree`,
Semantics.lean): a decided `.ok` outcome of heap-free code carries exactly
the input world. The predicates are syntactic and kernel-computable, so
concrete modules discharge the hypotheses by `rfl` — that is the frame
theorem lifting pure `CallsTo` specs into the stateful `CallsIn` world
(`CallsTo.callsIn_frame`, Surface.lean). Heap READS (subscript reads,
membership, `len`, `.get`, `==`, truthiness) are world-preserving and stay
inside the fragment; loud and raising arms are vacuous for
`.ok`-invariance. -/

/-- `Run.OkW p x`: every decided `.ok` outcome of `x` lands in a state
satisfying `p` (nothing is claimed about `.exn`/`.timeout`/`.unsupported`
— the ok-chain is all the world-invariance consumers need). -/
def Run.OkW {σ α : Type} (p : σ → Prop) (x : Run σ α) : Prop :=
  ∀ s a, x = .ok s a → p s

namespace Run.OkW

theorem ok {σ α : Type} {p : σ → Prop} {s : σ} (h : p s) (a : α) :
    Run.OkW p (.ok s a) := fun _ _ he => by cases he; exact h

/-- `ok` with the frame-world predicate pinned in the statement shape —
the leaf the `worldInv` cases use (the generic `ok` at a `rfl` argument
commits the elaborator to a wrong higher-order predicate). -/
theorem okF {α : Type} {w : World} {st : FrameState} (h : st.world = w) (a : α) :
    Run.OkW (fun s : FrameState => s.world = w) (.ok st a) :=
  fun _ _ he => by cases he; exact h

/-- `ok` with the world-equality predicate pinned (the `callIn` leaf). -/
theorem okA {α : Type} {w w' : World} (h : w' = w) (a : α) :
    Run.OkW (fun x : World => x = w) (.ok w' a) :=
  fun _ _ he => by cases he; exact h

theorem exn {σ α : Type} {p : σ → Prop} {s : σ} {e : PyErr} :
    Run.OkW p (.exn s e : Run σ α) := fun _ _ he => by cases he

theorem timeout {σ α : Type} {p : σ → Prop} :
    Run.OkW p (.timeout : Run σ α) := fun _ _ he => by cases he

theorem unsupported {σ α : Type} {p : σ → Prop} {msg : String} :
    Run.OkW p (.unsupported msg : Run σ α) := fun _ _ he => by cases he

theorem mono {σ α : Type} {p q : σ → Prop} {x : Run σ α}
    (hpq : ∀ s, p s → q s) (h : Run.OkW p x) : Run.OkW q x :=
  fun s a he => hpq s (h s a he)

theorem bind {σ α β : Type} {p : σ → Prop} {x : Run σ α}
    {f : σ → α → Run σ β} (hx : Run.OkW p x)
    (hf : ∀ s a, p s → Run.OkW p (f s a)) : Run.OkW p (x.bind f) := by
  intro s' b h
  rw [Run.bind_eq_ok] at h
  obtain ⟨s, a, hx', hf'⟩ := h
  exact hf s a (hx s a hx') s' b hf'

theorem ite {σ α : Type} {p : σ → Prop} {c : Prop} [Decidable c]
    {x y : Run σ α} (hx : Run.OkW p x) (hy : Run.OkW p y) :
    Run.OkW p (if c then x else y) := by
  by_cases h : c
  · simpa only [if_pos h] using hx
  · simpa only [if_neg h] using hy

theorem liftRes {σ α : Type} {p : σ → Prop} {s : σ} (h : p s) (r : Res α) :
    Run.OkW p (Run.liftRes s r) := by
  intro s' a he
  rw [Run.liftRes_eq_ok] at he
  exact he.1 ▸ h

/-- `liftRes` with the frame-world predicate pinned (see `okF`). -/
theorem liftResF {α : Type} {w : World} {st : FrameState} (h : st.world = w)
    (r : Res α) :
    Run.OkW (fun s : FrameState => s.world = w) (Run.liftRes st r) := by
  intro s' a he
  rw [Run.liftRes_eq_ok] at he
  exact he.1 ▸ h

/-- A nested call whose out-world is pinned rides `withLocals` into a
frame whose world is pinned. -/
theorem withLocals {α : Type} {w : World} {l : REnv} {x : Run World α}
    (h : Run.OkW (· = w) x) :
    Run.OkW (fun st : FrameState => st.world = w) (Run.withLocals l x) := by
  intro st a he
  rw [Run.withLocals_eq_ok] at he
  obtain ⟨w', hx', rfl⟩ := he
  exact h w' a hx'

/-- A body run with pinned frame-world projects to a pinned out-world. -/
theorem toWorld {α : Type} {w : World} {x : Run FrameState α}
    (h : Run.OkW (fun st : FrameState => st.world = w) x) :
    Run.OkW (· = w) (Run.toWorld x) := by
  intro w' a he
  rw [Run.toWorld_eq_ok] at he
  obtain ⟨st, hx', rfl⟩ := he
  exact h st a hx'

end Run.OkW

/-- **Conditional world invariance**, one conjunction over the mutual
block (same order as `fuelMono`, minus `evalDictItems` — dict literals are
outside the fragment, so that conjunct would be vacuous): in a heap-free
module, every decided `.ok` outcome of heap-free code carries the input
world unchanged — `callIn`'s conjunct says a nested call returns exactly
the world it was given. See the section comment for scope. -/
theorem worldInv (m : Module) (hm : m.heapFree = true) (fuel : Nat) :
    (∀ (st : FrameState) (e : Expr), e.heapFree = true →
      Run.OkW (·.world = st.world) (evalExpr m fuel st e)) ∧
    (∀ (st : FrameState) (es : List Expr), Expr.heapFreeList es = true →
      Run.OkW (·.world = st.world) (evalExprs m fuel st es)) ∧
    (∀ (st : FrameState) (op : BoolOp) (e : Expr) (rest : List Expr),
        e.heapFree = true → Expr.heapFreeList rest = true →
      Run.OkW (·.world = st.world) (evalBoolChain m fuel st op e rest)) ∧
    (∀ (st : FrameState) (lhs : RVal) (ops : List CmpOp) (cs : List Expr),
        Expr.heapFreeList cs = true →
      Run.OkW (·.world = st.world) (evalCompareChain m fuel st lhs ops cs)) ∧
    (∀ (st : FrameState) (s : Stmt), s.heapFree = true →
      Run.OkW (·.world = st.world) (execStmt m fuel st s)) ∧
    (∀ (st : FrameState) (ss : List Stmt), Stmt.heapFreeList ss = true →
      Run.OkW (·.world = st.world) (execStmts m fuel st ss)) ∧
    (∀ (st : FrameState) (test : Expr) (body orelse : List Stmt),
        test.heapFree = true → Stmt.heapFreeList body = true →
        Stmt.heapFreeList orelse = true →
      Run.OkW (·.world = st.world) (execWhile m fuel st test body orelse)) ∧
    (∀ (w : World) (fname : String) (args : Array RVal),
      Run.OkW (· = w) (callIn m fuel w fname args)) ∧
    (∀ (st : FrameState) (target : Expr) (xs : List RVal) (body : List Stmt),
        Stmt.heapFreeList body = true →
      Run.OkW (·.world = st.world) (execFor m fuel st target xs body)) ∧
    (∀ (st : FrameState) (target : Expr) (a : Addr) (i : Nat) (body : List Stmt),
        Stmt.heapFreeList body = true →
      Run.OkW (·.world = st.world) (execForList m fuel st target a i body)) ∧
    -- generalized 2026-08-15 from `attr = "get"` to the whole
    -- `heapFreeAttr` whitelist (docs/backlog.md)
    (∀ (st : FrameState) (a : Addr) (attr : String) (args : List Expr),
        heapFreeAttr attr = true → Expr.heapFreeList args = true →
      Run.OkW (·.world = st.world) (execAttrCall m fuel st a attr args)) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro st e _ s a h; simp [evalExpr] at h
    · intro st es _ s a h; simp [evalExprs] at h
    · intro st op e rest _ _ s a h; simp [evalBoolChain] at h
    · intro st lhs ops cs _ s a h; simp [evalCompareChain] at h
    · intro st s _ s' a h; simp [execStmt] at h
    · intro st ss _ s a h; simp [execStmts] at h
    · intro st test body orelse _ _ _ s a h; simp [execWhile] at h
    · intro w fname args w' a h; simp [callIn] at h
    · intro st target xs body _ s a h; simp [execFor] at h
    · intro st target a i body _ s' a' h; simp [execForList] at h
    · intro st a attr args _ _ s' a' h; simp [execAttrCall] at h
  | succ fuel ih =>
    obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihCall, ihFor, ihForL, ihAttrC⟩ := ih
    have wtrans : ∀ (st st₁ : FrameState), st₁.world = st.world →
        ∀ s : FrameState, s.world = st₁.world → s.world = st.world :=
      fun _ _ h₁ _ h₂ => h₂.trans h₁
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- evalExpr
    · intro st e hfree
      cases e with
      | constant c _ => simp only [evalExpr]; exact .okF rfl _
      | namedExpr id v _ => simp [Expr.heapFree] at hfree
      | name id _ =>
        simp only [evalExpr]
        cases Env.lookup st.locals id with
        | some v => exact .okF rfl _
        | none =>
          cases lookupG (moduleGlobals m).1 id with
          | some vv =>
            cases vv with
            | some v => exact .okF rfl _
            | none =>
              -- pass 3: the poisoned-arm live view — a hit is a pure
              -- world read, a miss the old refusal
              cases Env.lookup st.world.globals id with
              | some v => exact .okF rfl _
              | none => exact .unsupported
          | none =>
            -- findFunction / findClass / findNamedTuple / isBuiltinName /
            -- isModuleDunder / the pass-3 live view / analysable → NameError
            refine .ite .unsupported (.ite .unsupported (.ite .unsupported
              (.ite .unsupported (.ite .unsupported ?_))))
            cases Env.lookup st.world.globals id with
            | some v => exact .okF rfl _
            -- the unmodelled-CPython-builtin refusal (2026-08-13) sits in
            -- front of the analysable/NameError fork
            | none => exact .ite .unsupported (.ite .exn .unsupported)
      | binOp l op r _ =>
        simp only [Expr.heapFree, Bool.and_eq_true] at hfree
        simp only [evalExpr]
        exact .bind (ihE st l hfree.1) fun st₁ a h₁ =>
          .bind ((ihE st₁ r hfree.2).mono (wtrans st st₁ h₁)) fun st₂ b h₂ =>
            .liftResF h₂ _
      | unaryOp op operand _ =>
        simp only [Expr.heapFree] at hfree
        simp only [evalExpr]
        exact .bind (ihE st operand hfree) fun st₁ v h₁ => .liftResF h₁ _
      | boolOp op values _ =>
        simp only [Expr.heapFree] at hfree
        simp only [evalExpr]
        cases hv : values.toList with
        | nil => exact .unsupported
        | cons e0 es =>
          rw [hv] at hfree
          simp only [Expr.heapFreeList, Bool.and_eq_true] at hfree
          exact ihB st op e0 es hfree.1 hfree.2
      | compare l ops comparators _ =>
        simp only [Expr.heapFree, Bool.and_eq_true] at hfree
        simp only [evalExpr]
        exact .bind (ihE st l hfree.1) fun st₁ a h₁ =>
          (ihC st₁ a ops.toList comparators.toList hfree.2).mono (wtrans st st₁ h₁)
      | call cf cargs ckw cu _ =>
        cases cu with
        | some reason => simp only [evalExpr]; exact .unsupported
        | none =>
          -- H6: every `heapFree` call arm's FIRST conjunct pins
          -- `ckw.isEmpty`, so the keyword gate reduces to the positional
          -- path; in the catch-all arms both branches are loud
          cases cf <;> try (simp only [evalExpr]; exact .ite .unsupported .unsupported)
          case «attribute» recv attr spa =>
            -- the method tier: the FRAGMENT admits the `heapFreeAttr`
            -- whitelist — `.get` (a heap READ) plus the PURE str methods
            -- (2026-08-15, generalized from `.get`-only). `hfree` pins the
            -- attribute to the whitelist, which kills every MUTATING
            -- branch (`.clear`/`.append`/`.pop`/`.insert`); instance
            -- receivers dispatch to classes, and a heap-free module HAS
            -- no classes (hm), so the method branch is vacuous.
            simp only [Expr.heapFree, Bool.and_eq_true] at hfree
            obtain ⟨⟨⟨hkw, hattr⟩, hrecv⟩, hargsF⟩ := hfree
            -- pass 6: the trace-clock fork dies at its FIRST conjunct
            -- (`attr == "time"`, and `time` is deliberately outside the
            -- whitelist — the attr test sits outside the receiver match
            -- precisely so this closes before the receiver is evaluated)
            have hclk : isClockCall m st recv attr = false :=
              isClockCall_of_heapFreeAttr hattr
            simp only [evalExpr, hkw, if_true, hclk,
              Bool.false_eq_true, if_false]
            refine .bind (ihE st recv hrecv) fun st₁ r h₁ => ?_
            cases r <;>
              first
              | exact .unsupported
              | exact ((ihAttrC st₁ _ attr cargs.toList hattr hargsF).mono
                  (wtrans st st₁ h₁))
              | skip
            case ntuple tn fs xs =>
              -- heap-free: no classes ⇒ the plan never dispatches
              dsimp only
              rcases ntupleCallPlan_heapFree hm tn fs attr with hp | ⟨msg, hp⟩ <;>
                rw [hp]
              · exact .exn
              · exact .unsupported
            case str sv =>
              -- H5 strings (2026-08-15): the PURE str methods are IN the
              -- fragment now. Every in-tier arm is argument evaluation
              -- followed by `Run.liftRes` on a TOTAL PURE worker —
              -- strings are immutable VALUES, so nothing allocates and
              -- nothing mutates — while every arity miss is an `.exn`
              -- and every out-of-tier name a decided refusal.
              -- All five in-tier plans have ONE shape — evaluate the
              -- arguments, then decide purely — so one recipe closes
              -- them: `split` opens the arity matcher (and, for
              -- `.index`, the nested start/end `ite`), and every leaf is
              -- a `liftRes` of a pure worker, the faithful arity `.exn`,
              -- or a decided refusal. `split` rather than `cases` on the
              -- argument list: the recipe must not depend on how the
              -- 4-pattern matcher happened to compile.
              dsimp only
              have hvs := (ihEs st₁ cargs.toList hargsF).mono (wtrans st st₁ h₁)
              cases strCallPlan attr <;>
                first
                | exact .unsupported
                | (refine .bind hvs fun st₂ vs h₂ => ?_
                   split <;> (try split) <;>
                     first
                     | exact .liftResF h₂ _
                     | exact .exn
                     | exact .unsupported)
          case name fname _ =>
            -- H2: `sorted` ALLOCATES its result, so the fragment excludes
            -- it (hfree carries `fname != "sorted"` — the branch is
            -- rewritten away before the ite walk)
            simp only [Expr.heapFree, Bool.and_eq_true] at hfree
            obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hkw, hns⟩, hnn⟩, hne⟩, hnc⟩, hna⟩, hnl⟩, hnset⟩, hnpr⟩, hnlst⟩, hndct⟩, hflE⟩ := hfree
            have hs : (fname == "sorted") = false := by
              cases hbe : fname == "sorted"
              · rfl
              · rw [bne, hbe] at hns; simp at hns
            -- H4: `next` STEPS a generator and `enumerate`/`count`
            -- ALLOCATE an iterator object; H6 adds `any`/`all` (an
            -- unguarded short-circuit drain) — the fragment excludes all
            -- five, the same syntactic carve-out as `sorted`
            have hnx : (fname == "next") = false := by
              cases hbe : fname == "next"
              · rfl
              · rw [bne, hbe] at hnn; simp at hnn
            have hex : (fname == "enumerate") = false := by
              cases hbe : fname == "enumerate"
              · rfl
              · rw [bne, hbe] at hne; simp at hne
            have hcx : (fname == "count") = false := by
              cases hbe : fname == "count"
              · rfl
              · rw [bne, hbe] at hnc; simp at hnc
            have hay : (fname == "any") = false := by
              cases hbe : fname == "any"
              · rfl
              · rw [bne, hbe] at hna; simp at hna
            have hal : (fname == "all") = false := by
              cases hbe : fname == "all"
              · rfl
              · rw [bne, hbe] at hnl; simp at hnl
            have hsetx : (fname == "set") = false := by
              cases hbe : fname == "set"
              · rfl
              · rw [bne, hbe] at hnset; simp at hnset
            -- 2026-08-13: `print` MUTATES `World.stdout` (the one effect
            -- the interpreter performs), so the fragment excludes it the
            -- same syntactic way, and its branch is rewritten away below
            have hprx : (fname == "print") = false := by
              cases hbe : fname == "print"
              · rfl
              · rw [bne, hbe] at hnpr; simp at hnpr
            -- `list(…)` ALLOCATES a fresh heap object (2026-08-13,
            -- list comprehensions) — the `sorted` carve-out again
            have hlstx : (fname == "list") = false := by
              cases hbe : fname == "list"
              · rfl
              · rw [bne, hbe] at hnlst; simp at hnlst
            -- `dict(…)` ALLOCATES too (2026-08-13)
            have hdctx : (fname == "dict") = false := by
              cases hbe : fname == "dict"
              · rfl
              · rw [bne, hbe] at hndct; simp at hndct
            simp only [evalExpr, hkw, eq_self_iff_true, if_true]
            have hargs : Run.OkW (·.world = st.world) (evalExprs m fuel st cargs.toList) :=
              ihEs st cargs.toList hflE
            cases Env.lookup st.locals fname with
            | some v =>
              cases v <;>
                first
                | exact .unsupported
                | exact .bind hargs fun st₁ _ h₁ => .exn
                | skip
              case ref a =>
                -- H7 (+pass 3): hm's function-body walk AND top-level
                -- def-freedom discharge the guard — the closure call is
                -- unreachable in a heap-free module
                refine .bind hargs fun st₁ vs h₁ => ?_
                simp only [Module.heapFree_funs hm, Module.heapFree_topDefFree hm,
                  Bool.and_self, eq_self_iff_true, if_true]
                exact .exn
            | none =>
              cases lookupG (moduleGlobals m).1 fname with
              | some vv =>
                cases vv with
                | some v => cases v <;> exact .bind hargs fun st₁ _ h₁ => .exn
                | none =>
                  -- pass 3: the poisoned-arm live view — the guard kills
                  -- the closure dispatch in a heap-free module
                  cases Env.lookup st.world.globals fname with
                  | none => exact .unsupported
                  | some v =>
                    cases v <;>
                      first
                        | exact .bind hargs fun st₁ _ h₁ => .exn
                        | skip
                    case ref a =>
                      refine .bind hargs fun st₁ vs h₁ => ?_
                      simp only [Module.heapFree_funs hm, Module.heapFree_topDefFree hm,
                        Bool.and_self, eq_self_iff_true, if_true]
                      exact .exn
              | none =>
                -- a heap-free module has no classes: the instantiation
                -- branch reduces away; the def/namedtuple collision guard
                -- stays an undecided (walked) ite, and namedtuple
                -- CONSTRUCTION is a pure value — world-preserving
                simp only [hs, hnx, hex, hcx, hay, hal, hsetx, hprx, hlstx, hdctx,
                  findClass_heapFree hm fname,
                  Option.isSome_none, Bool.false_or, Bool.false_eq_true, if_false]
                refine .ite (.ite .unsupported (.bind hargs fun st₁ vs h₁ => ?_)) ?_
                · exact ((ihCall st₁.world fname vs.toArray).withLocals
                    (l := st₁.locals)).mono
                      (fun s hs => (show s.world = st₁.world from hs).trans h₁)
                · cases hnt : findNamedTuple m fname with
                  | some nt =>
                    exact .bind hargs fun st₁ vs h₁ => .ite (.okF h₁ _) .exn
                  | none =>
                    refine .ite (.bind hargs fun st₁ vs h₁ => ?_) ?_
                    · cases vs with
                      | nil => exact .exn
                      | cons v rest =>
                        cases rest with
                        | nil => exact .liftResF h₁ _
                        | cons _ _ => exact .exn
                    · -- max/min (H6): the single-generator-argument arm
                      -- drains behind the `moduleGenFree` GUARD, which a
                      -- heap-free module discharges (`heapFree_genFree`)
                      -- — every other shape is the pure fold
                      refine .ite (.bind hargs fun st₁ vs h₁ => ?_) ?_
                      · cases vs with
                        | nil => exact .liftResF h₁ _
                        | cons v vtail =>
                          cases v <;> try exact .liftResF h₁ _
                          case ref a =>
                            cases vtail with
                            | cons _ _ => exact .liftResF h₁ _
                            | nil =>
                              dsimp only
                              cases Heap.get? st₁.world.heap a with
                              | none => exact .liftResF h₁ _
                              | some obj =>
                                cases obj <;> try exact .liftResF h₁ _
                                case generator q l c stat =>
                                  simp only [Module.heapFree_genFree hm,
                                    eq_self_iff_true, if_true]
                                  exact .unsupported
                      refine .ite (.bind hargs fun st₁ vs h₁ => ?_) ?_
                      · cases vs with
                        | nil => exact .liftResF h₁ _
                        | cons v vtail =>
                          cases v <;> try exact .liftResF h₁ _
                          case ref a =>
                            cases vtail with
                            | cons _ _ => exact .liftResF h₁ _
                            | nil =>
                              dsimp only
                              cases Heap.get? st₁.world.heap a with
                              | none => exact .liftResF h₁ _
                              | some obj =>
                                cases obj <;> try exact .liftResF h₁ _
                                case generator q l c stat =>
                                  simp only [Module.heapFree_genFree hm,
                                    eq_self_iff_true, if_true]
                                  exact .unsupported
                      refine .ite (.bind hargs fun st₁ vs h₁ => ?_) ?_
                      · cases vs with
                        | nil => exact .exn
                        | cons v rest =>
                          cases rest with
                          | nil => exact .liftResF h₁ _
                          | cons _ _ => exact .exn
                      · -- `int`, then the pass-3 trio `sum`/`tuple`/
                        -- `range` (value folds; the generator drains sit
                        -- behind the `moduleGenFree` guard, discharged by
                        -- `heapFree_genFree`), then `next` (rewritten
                        -- away by `hnx` — outside the fragment), the H5
                        -- pair `ord`/`chr`, then print / module dunder /
                        -- NameError / loud
                        refine .ite (.bind hargs fun st₁ vs h₁ => ?_)
                          (.ite (.bind hargs fun st₁ vs h₁ => ?_)
                            (.ite (.bind hargs fun st₁ vs h₁ => ?_)
                              (.ite (.bind hargs fun st₁ vs h₁ => .liftResF h₁ _)
                                (.ite (.bind hargs fun st₁ vs h₁ => ?_)
                                  (.ite (.bind hargs fun st₁ vs h₁ => ?_)
                                    (.ite (.bind hargs fun st₁ vs h₁ => ?_)
                                      (.ite .unsupported
                                        (.ite .unsupported ?_))))))))
                        · cases vs with
                          | nil => exact .okF h₁ _
                          | cons v rest =>
                            cases rest with
                            | nil => exact .liftResF h₁ _
                            | cons _ _ => exact .unsupported
                        · -- sum
                          cases sumArgs vs with
                          | none => exact .exn
                          | some pr =>
                            obtain ⟨v, start⟩ := pr
                            dsimp only
                            cases start <;> try exact .exn
                            all_goals
                              cases v <;> try exact .liftResF h₁ _
                            all_goals try exact .exn
                            all_goals
                              case ref a =>
                                dsimp only
                                cases Heap.get? st₁.world.heap a with
                                | none => exact .unsupported
                                | some obj =>
                                  cases obj <;>
                                    first
                                      | exact .liftResF h₁ _
                                      | exact .unsupported
                                      | exact .exn
                                      | skip
                                  case generator q l c stat =>
                                    simp only [Module.heapFree_genFree hm,
                                      eq_self_iff_true, if_true]
                                    exact .unsupported
                        · -- tuple
                          cases vs with
                          | nil => exact .okF h₁ _
                          | cons v vtail =>
                            cases vtail with
                            | cons _ _ => exact .exn
                            | nil =>
                              dsimp only
                              cases v <;>
                                first
                                  | exact .okF h₁ _
                                  | exact .liftResF h₁ _
                                  | exact .exn
                                  | skip
                              case ref a =>
                                dsimp only
                                cases Heap.get? st₁.world.heap a with
                                | none => exact .unsupported
                                | some obj =>
                                  cases obj <;>
                                    first
                                      | exact .okF h₁ _
                                      | exact .unsupported
                                      | exact .exn
                                      | skip
                                  case generator q l c stat =>
                                    simp only [Module.heapFree_genFree hm,
                                      eq_self_iff_true, if_true]
                                    exact .unsupported
                        · cases vs with
                          | nil => exact .exn
                          | cons v rest =>
                            cases rest with
                            | nil => exact .liftResF h₁ _
                            | cons _ _ => exact .exn
                        · cases vs with
                          | nil => exact .exn
                          | cons v rest =>
                            cases rest with
                            | nil => exact .liftResF h₁ _
                            | cons _ _ => exact .exn
                        · -- str (pass 8, §the cast tier): pure worker
                          cases vs with
                          | nil => exact .okF h₁ _
                          | cons v rest =>
                            cases rest with
                            | nil => exact .liftResF h₁ _
                            | cons _ _ => exact .unsupported
                        · -- the pass-3 absent-arm live view: the guard
                          -- (funs + top-level def-freedom, both from hm)
                          -- kills the closure dispatch
                          cases Env.lookup st.world.globals fname with
                          | none => exact .ite .unsupported (.ite .exn .unsupported)
                          | some v =>
                            cases v <;>
                              first
                                | exact .bind hargs fun st₁ _ h₁ => .exn
                                | skip
                            case ref a =>
                              refine .bind hargs fun st₁ vs h₁ => ?_
                              simp only [Module.heapFree_funs hm,
                                Module.heapFree_topDefFree hm,
                                Bool.and_self, eq_self_iff_true, if_true]
                              exact .exn
      | genExp elt tgt it ifs wb _ =>
        -- H4: a genexp ALLOCATES a generator — outside the fragment
        simp [Expr.heapFree] at hfree
      | list elts _ =>
        -- H2: list displays ALLOCATE — outside the fragment
        simp [Expr.heapFree] at hfree
      | tuple elts _ =>
        simp only [Expr.heapFree] at hfree
        simp only [evalExpr]
        exact .bind (ihEs st elts.toList hfree) fun st₁ vs h₁ => .okF h₁ _
      | subscript v idx _ =>
        simp only [Expr.heapFree, Bool.and_eq_true] at hfree
        simp only [evalExpr]
        exact .bind (ihE st v hfree.1) fun st₁ c h₁ =>
          .bind ((ihE st₁ idx hfree.2).mono (wtrans st st₁ h₁)) fun st₂ i h₂ =>
            .liftResF h₂ _
      | dict keys values _ =>
        -- outside the fragment: `heapFree = false` refutes the hypothesis
        simp [Expr.heapFree] at hfree
      | ifExp t b o _ =>
        simp only [Expr.heapFree, Bool.and_eq_true] at hfree
        simp only [evalExpr]
        refine .bind (ihE st t hfree.1.1) fun st₁ tv h₁ => ?_
        refine .bind (.liftResF h₁ _) fun st₂ cond h₂ => ?_
        exact .ite ((ihE st₂ b hfree.1.2).mono (wtrans st st₂ h₂))
          ((ihE st₂ o hfree.2).mono (wtrans st st₂ h₂))
      | slice v l u stp _ =>
        -- H5 strings: components bind, then the PURE `sliceVal` (str
        -- slices are values; allocating receivers refuse loudly)
        simp only [Expr.heapFree, Bool.and_eq_true] at hfree
        simp only [evalExpr]
        refine .bind (ihE st v hfree.1.1.1) fun st₁ cv h₁ => ?_
        refine .bind ((ihE st₁ l hfree.1.1.2).mono (wtrans st st₁ h₁))
          fun st₂ lv h₂ => ?_
        refine .bind ((ihE st₂ u hfree.1.2).mono (wtrans st st₂ h₂))
          fun st₃ uv h₃ => ?_
        exact .bind ((ihE st₃ stp hfree.2).mono (wtrans st st₃ h₃))
          fun st₄ sv h₄ => .liftResF h₄ _
      | «attribute» recv attr _ =>
        -- attribute READ (H3): a pure heap read — world-preserving; the
        -- bound-method/AttributeError forks are all ok-free or pinned
        simp only [Expr.heapFree] at hfree
        simp only [evalExpr]
        refine .bind (ihE st recv hfree) fun st₁ r h₁ => ?_
        cases r <;>
          first
          | exact .unsupported
          | exact .liftResF h₁ _
          | exact fun s₂ v₂ he => (attrReadResult_ok he) ▸ h₁
      | unsupported pyKind text _ => simp only [evalExpr]; exact .unsupported
    -- evalExprs
    · intro st es hfree
      cases es with
      | nil => simp only [evalExprs]; exact .okF rfl _
      | cons e rest =>
        simp only [Expr.heapFreeList, Bool.and_eq_true] at hfree
        simp only [evalExprs]
        exact .bind (ihE st e hfree.1) fun st₁ v h₁ =>
          .bind ((ihEs st₁ rest hfree.2).mono (wtrans st st₁ h₁)) fun st₂ vs h₂ =>
            .okF h₂ _
    -- evalBoolChain
    · intro st op e rest hfree hrest
      simp only [evalBoolChain]
      refine .bind (ihE st e hfree) fun st₁ v h₁ => ?_
      cases rest with
      | nil => exact .okF h₁ _
      | cons e' rest' =>
        simp only [Expr.heapFreeList, Bool.and_eq_true] at hrest
        refine .bind (.liftResF h₁ _) fun st₂ b h₂ => ?_
        cases op with
        | and =>
          exact .ite ((ihB st₂ .and e' rest' hrest.1 hrest.2).mono
            (wtrans st st₂ h₂)) (.okF h₂ _)
        | or =>
          exact .ite (.okF h₂ _) ((ihB st₂ .or e' rest' hrest.1 hrest.2).mono
            (wtrans st st₂ h₂))
    -- evalCompareChain
    · intro st lhs ops cs hfree
      cases ops with
      | nil =>
        cases cs with
        | nil => simp only [evalCompareChain]; exact .okF rfl _
        | cons c cs' => simp only [evalCompareChain]; exact .unsupported
      | cons op ops' =>
        cases cs with
        | nil => simp only [evalCompareChain]; exact .unsupported
        | cons e rest =>
          simp only [Expr.heapFreeList, Bool.and_eq_true] at hfree
          simp only [evalCompareChain]
          refine .bind (ihE st e hfree.1) fun st₁ rhs h₁ => ?_
          refine .bind (.liftResF h₁ _) fun st₂ b h₂ => ?_
          exact .ite ((ihC st₂ rhs ops' rest hfree.2).mono (wtrans st st₂ h₂))
            (.okF h₂ _)
    -- execStmt
    · intro st s hfree
      cases s with
      | defStmt name params ao lo hg ig body caps _ =>
        simp [Stmt.heapFree] at hfree
      | yieldFromStmt v _ =>
        -- pass 5: OUT of the fragment (docs/memory-model.md §yield from)
        simp [Stmt.heapFree] at hfree
      | tryStmt body excName handler tu _ =>
        -- OUT of the fragment (as-built delta, docs/memory-model.md
        -- §exceptions): the handler resumes from the body's retained
        -- `.exn` state, invisible to the ok-only invariant
        simp [Stmt.heapFree] at hfree
      | importFrom mod names star _ =>
        -- Pass 0 (§import forms): IN the fragment, vacuously — the arm
        -- never decides `.ok` (it raises, fuel-free); the `raiseStmt`
        -- argument. The future modeled-module BINDING arm must flip
        -- `Stmt.heapFree` to `false` or re-prove this — the recorded
        -- review point.
        simp only [execStmt]
        exact .exn
      | raiseStmt exc cause _ =>
        -- IN the fragment, vacuously: the raise arm never decides `.ok`
        simp only [execStmt]
        cases cause with
        | some c => exact .unsupported
        | none =>
          cases exc with
          | none => exact .unsupported
          | some e =>
            cases e <;> try exact .unsupported
            case name id _ =>
              refine .ite .unsupported ?_
              cases findClass m id with
              | none => exact .unsupported
              | some p =>
                obtain ⟨ci, c⟩ := p
                exact .ite .exn .unsupported
      | assertStmt test msg _ =>
        -- the tail batch: IN the fragment and NOT vacuously — the
        -- passing path decides `.ok` with the input state untouched
        -- (nothing is allocated or mutated), the failing path raises.
        simp only [Stmt.heapFree, Bool.and_eq_true] at hfree
        simp only [execStmt]
        refine .bind (ihE st test hfree.1) fun st₁ t h₁ => ?_
        refine .bind (.liftResF h₁ _) fun st₂ b h₂ => ?_
        refine .ite (.okF h₂ _) ?_
        cases msg with
        | none => exact .exn
        | some e =>
          -- `(Option.map Expr.heapFree (some e)).getD true` reduces
          -- definitionally, so hfree.2 IS `e.heapFree = true`
          refine .bind ((ihE st₂ e hfree.2).mono (wtrans st st₂ h₂))
            fun st₃ v h₃ => ?_
          cases printOne st₃.world.heap v with
          | none => exact .unsupported
          | some r => exact .exn
      | delStmt names _ =>
        -- del RECONCILED: IN the fragment and NOT vacuously — the ok
        -- path rewrites only `st.locals`, which is not a `World` field
        -- (the recorded design's `.okF` pricing); the miss path refuses.
        simp only [execStmt]
        cases delNames st.locals names.toList with
        | mk env miss =>
          cases miss with
          | none => exact .okF rfl _
          | some n => exact .unsupported
      | yieldStmt e _ => simp only [execStmt]; exact .unsupported
      | ret value _ =>
        cases value with
        | none => simp only [execStmt]; exact .okF rfl _
        | some e =>
          simp only [Stmt.heapFree] at hfree
          simp only [execStmt]
          exact .bind (ihE st e hfree) fun st₁ v h₁ => .okF h₁ _
      | assign targets value _ =>
        simp only [Stmt.heapFree, Bool.and_eq_true] at hfree
        simp only [execStmt]
        cases htl : targets.toList with
        | nil => exact .unsupported
        | cons t rest =>
          rw [htl] at hfree
          cases rest with
          | nil =>
            cases t
            case subscript dE kE sp => exact absurd hfree.1 (by simp)
            case «attribute» recvE attr sp => exact absurd hfree.1 (by simp)
            case tuple elts sp =>
              -- pass 4: the fragment admits only the all-names fork
              -- (`targetNames.isSome` — hfree's first conjunct), which is
              -- the unchanged pure path
              have h1 : (targetNames elts).isSome = true := hfree.1
              dsimp only
              rw [if_pos h1]
              exact .bind (ihE st value hfree.2) fun st₁ v h₁ =>
                .bind (.liftResF h₁ _) fun st₂ env' h₂ =>
                  fun _ _ he => by cases he; exact h₂
            all_goals
              exact .bind (ihE st value hfree.2) fun st₁ v h₁ =>
                .bind (.liftResF h₁ _) fun st₂ env' h₂ =>
                  fun _ _ he => by cases he; exact h₂
          | cons t2 rest2 =>
            cases t <;> exact .unsupported
      | augAssign target op value _ =>
        cases target
        case «attribute» recvE attr _ =>
          -- pass 4: an attribute-target `+=` STORES — out of the fragment
          simp [Stmt.heapFree] at hfree
        case name id _ =>
          simp only [Stmt.heapFree, Bool.and_eq_true] at hfree
          simp only [execStmt]
          cases Env.lookup st.locals id with
          | none => exact .exn
          | some old =>
            cases old <;>
              first
              | exact .unsupported
              | exact .bind (ihE st value hfree.2) fun st₁ v h₁ =>
                  .bind (.liftResF h₁ _) fun st₂ r h₂ =>
                    fun _ _ he => by cases he; exact h₂
        all_goals simp only [execStmt]; exact .unsupported
      | whileLoop test body orelse _ =>
        simp only [Stmt.heapFree, Bool.and_eq_true] at hfree
        simp only [execStmt]
        exact ihW st test body.toList orelse.toList hfree.1.1 hfree.1.2 hfree.2
      | forStmt target iter body orelse _ =>
        simp only [Stmt.heapFree, Bool.and_eq_true] at hfree
        simp only [execStmt]
        cases orelse.toList with
        | cons o os => exact .unsupported
        | nil =>
          refine .bind (ihE st iter hfree.1.1) fun st₁ it h₁ => ?_
          cases it with
          | none => exact .exn
          | bool b => exact .exn
          | int n => exact .exn
          | str s =>
            -- H5 iteration: a str's code points are a pure snapshot —
            -- the loop preserves the world exactly when the body does
            exact (ihFor st₁ target _ body.toList hfree.1.2).mono
              (wtrans st st₁ h₁)
          | listV xs =>
            exact (ihFor st₁ target _ body.toList hfree.1.2).mono
              (wtrans st st₁ h₁)
          | tuple xs =>
            exact (ihFor st₁ target _ body.toList hfree.1.2).mono
              (wtrans st st₁ h₁)
          | ntuple tn fs xs =>
            exact (ihFor st₁ target _ body.toList hfree.1.2).mono
              (wtrans st st₁ h₁)
          | rangeV lo hi step =>
            -- pass 3: materialization is a pure liftRes; the loop is the
            -- ordinary value-sequence `for`
            refine .bind (.liftResF h₁ _) fun st₂ xs h₂ => ?_
            exact (ihFor st₂ target _ body.toList hfree.1.2).mono
              (wtrans st st₂ h₂)
          | ref a =>
            -- H2: the list cursor (referent dispatch inside) preserves
            -- the world when the body does
            exact (ihForL st₁ target a 0 body.toList hfree.1.2).mono
              (wtrans st st₁ h₁)
      | ifStmt test body orelse _ =>
        simp only [Stmt.heapFree, Bool.and_eq_true] at hfree
        simp only [execStmt]
        refine .bind (ihE st test hfree.1.1) fun st₁ t h₁ => ?_
        refine .bind (.liftResF h₁ _) fun st₂ b h₂ => ?_
        exact .ite ((ihSs st₂ body.toList hfree.1.2).mono (wtrans st st₂ h₂))
          ((ihSs st₂ orelse.toList hfree.2).mono (wtrans st st₂ h₂))
      | exprStmt e _ =>
        simp only [Stmt.heapFree] at hfree
        simp only [execStmt]
        exact .bind (ihE st e hfree) fun st₁ v h₁ => .okF h₁ _
      | pass _ => simp only [execStmt]; exact .okF rfl _
      | brk _ => simp only [execStmt]; exact .okF rfl _
      | cont _ => simp only [execStmt]; exact .okF rfl _
      | unsupported pyKind text _ => simp only [execStmt]; exact .unsupported
    -- execStmts
    · intro st ss hfree
      cases ss with
      | nil => simp only [execStmts]; exact .okF rfl _
      | cons s rest =>
        simp only [Stmt.heapFreeList, Bool.and_eq_true] at hfree
        simp only [execStmts]
        refine .bind (ihS st s hfree.1) fun st₁ flow h₁ => ?_
        cases flow with
        | next => exact (ihSs st₁ rest hfree.2).mono (wtrans st st₁ h₁)
        | ret v => exact .okF h₁ _
        | brk => exact .okF h₁ _
        | cont => exact .okF h₁ _
    -- execWhile
    · intro st test body orelse htest hbody horelse
      simp only [execWhile]
      refine .bind (ihE st test htest) fun st₁ t h₁ => ?_
      refine .bind (.liftResF h₁ _) fun st₂ b h₂ => ?_
      refine .ite ?_ ((ihSs st₂ orelse horelse).mono (wtrans st st₂ h₂))
      refine .bind ((ihSs st₂ body hbody).mono (wtrans st st₂ h₂))
        fun st₃ flow h₃ => ?_
      cases flow with
      | next =>
        exact (ihW st₃ test body orelse htest hbody horelse).mono
          (wtrans st st₃ h₃)
      | ret v => exact .okF h₃ _
      | brk => exact .okF h₃ _
      | cont =>
        exact (ihW st₃ test body orelse htest hbody horelse).mono
          (wtrans st st₃ h₃)
    -- callIn
    · intro w fname args
      simp only [callIn]
      cases hff : findFunction m fname with
      | none => exact .exn
      | some f =>
        -- H4: `f.isGenerator` is FALSE in a heap-free module (no
        -- generator defs — `Module.heapFree`'s third conjunct), so the
        -- allocating branch is rewritten away before the walk
        simp only [findFunction_notGen hm hff, Bool.false_eq_true, if_false]
        refine .ite .unsupported (.ite .unsupported (.ite .exn ?_))
        refine Run.OkW.toWorld ?_
        refine .bind (ihSs ⟨w, mkCallEnv f.params args⟩ f.body.toList
          (findFunction_heapFree hm hff)) fun st₁ flow h₁ => ?_
        cases flow with
        | ret v => exact .okF h₁ _
        | next => exact .okF h₁ _
        | brk => exact .unsupported
        | cont => exact .unsupported
    -- execFor
    · intro st target xs body hbody
      cases xs with
      | nil => simp only [execFor]; exact .okF rfl _
      | cons x rest =>
        simp only [execFor]
        refine .bind (.liftResF rfl _) fun st₁ env₁ h₁ => ?_
        refine .bind ((ihSs { st₁ with locals := env₁ } body hbody).mono
          (fun s hs => hs.trans h₁)) fun st₂ flow h₂ => ?_
        cases flow with
        | next => exact (ihFor st₂ target rest body hbody).mono (wtrans st st₂ h₂)
        | cont => exact (ihFor st₂ target rest body hbody).mono (wtrans st st₂ h₂)
        | brk => exact .okF h₂ _
        | ret v => exact .okF h₂ _
    -- execForList (H2: the live cursor READS the list; a heap-free body
    -- keeps the world pinned through every step)
    · intro st target a i body hbody
      simp only [execForList]
      cases Heap.get? st.world.heap a with
      | none => exact .unsupported
      | some o =>
        cases o with
        | cell cv => exact .unsupported
        | dict es ver => exact .unsupported
        | «instance» ci attrs => exact .exn
        | closure nm ps ao lo' hg ig bd cap => exact .unsupported
        | pyset zs => exact .unsupported
        | generator qn lo kk stt =>
          -- H4: a generator object cannot exist in a generator-free
          -- module, and the guard says so LOUDLY — which is exactly what
          -- keeps this theorem free of a heap-side invariant
          simp only [Module.heapFree_genFree hm, if_true]
          exact .unsupported
        | list xs =>
          refine .ite ?_ (.okF rfl _)
          refine .bind (.liftResF rfl _) fun st₁ env₁ h₁ => ?_
          refine .bind ((ihSs { st₁ with locals := env₁ } body hbody).mono
            (fun s hs => hs.trans h₁)) fun st₂ flow h₂ => ?_
          cases flow with
          | next => exact (ihForL st₂ target a (i + 1) body hbody).mono (wtrans st st₂ h₂)
          | cont => exact (ihForL st₂ target a (i + 1) body hbody).mono (wtrans st st₂ h₂)
          | brk => exact .okF h₂ _
          | ret v => exact .okF h₂ _
    -- execAttrCall (H3): in a heap-free module a WHITELISTED attribute
    -- plan is a heap READ or a decided refusal (`attrCallPlan_heapFree`)
    · intro st a attr args hattr hargs
      simp only [execAttrCall]
      rcases attrCallPlan_heapFree hm st.world.heap a hattr with
        hp | hp | hp | ⟨msg, hp⟩ <;> rw [hp]
      · refine .bind (ihEs st args hargs) fun st₂ vs h₂ => ?_
        cases vs with
        | nil => exact .exn
        | cons k rest =>
          cases rest with
          | nil => exact .liftResF h₂ _
          | cons d rest2 =>
            cases rest2 with
            | nil => exact .liftResF h₂ _
            | cons _ _ => exact .exn
      · exact .unsupported
      · exact .unsupported
      · exact .unsupported

/-- `evalExpr` world invariance, direct form (heap-free module and
expression). -/
theorem evalExpr_world {m : Module} {fuel : Nat} {st st' : FrameState}
    {e : Expr} {v : RVal} (hm : m.heapFree = true) (hfree : e.heapFree = true)
    (h : evalExpr m fuel st e = .ok st' v) :
    st'.world = st.world := (worldInv m hm fuel).1 st e hfree st' v h

/-- `evalExprs` world invariance, direct form. -/
theorem evalExprs_world {m : Module} {fuel : Nat} {st st' : FrameState}
    {es : List Expr} {vs : List RVal} (hm : m.heapFree = true)
    (hfree : Expr.heapFreeList es = true)
    (h : evalExprs m fuel st es = .ok st' vs) :
    st'.world = st.world := (worldInv m hm fuel).2.1 st es hfree st' vs h

/-- `execStmts` world invariance, direct form. -/
theorem execStmts_world {m : Module} {fuel : Nat} {st st' : FrameState}
    {ss : List Stmt} {flow : RFlow} (hm : m.heapFree = true)
    (hfree : Stmt.heapFreeList ss = true)
    (h : execStmts m fuel st ss = .ok st' flow) :
    st'.world = st.world := (worldInv m hm fuel).2.2.2.2.2.1 st ss hfree st' flow h

/-- `callIn` world invariance, direct form: in a heap-free module a nested
call hands back exactly the world it was given — the frame theorem's
engine (`CallsTo.callsIn_frame`, Surface.lean). -/
theorem callIn_world {m : Module} {fuel : Nat} {w w' : World} {fname : String}
    {args : Array RVal} {v : RVal} (hm : m.heapFree = true)
    (h : callIn m fuel w fname args = .ok w' v) :
    w' = w := (worldInv m hm fuel).2.2.2.2.2.2.2.1 w fname args w' v h

/-! ## The boundary-flip rescue lemma (docs/backlog.md, H2 step 3b)

Once `callFunction` thaws `Val.list` ARGUMENTS onto the heap
(`RVal.thawArgsH`), a `for` over a boundary-passed list runs the LIVE
cursor (`execForList`) instead of `execFor` over the transitional value
list — and the frozen-tail `for` induction pattern
(`Examples/python/sf_bound_for/proof.lean`) speaks `execFor`. The rescue:
over a heap-free module and a heap-free body, every iteration's world is
PINNED (`worldInv`), so the cursor's per-step re-read always sees the same
object — the live cursor IS `execFor` over the snapshot. -/

/-- The list element `execForList` reads at cursor `i` is the snapshot's
`i`-th element (bounds given). -/
private theorem getD_toList_getElem (xs : Array RVal) (i : Nat)
    (h : i < xs.size) : xs.getD i .none = xs.toList[i]'(by simpa using h) := by
  simp [Array.getD, h]

/-- **The live cursor is `execFor` on the snapshot** (pinned worlds): in a
heap-free module, iterating a heap list at `a` with a heap-free body from
cursor `i` is exactly `execFor` over the object's element snapshot from
`i` — same fuel, same outcome, states included. By induction on fuel: the
body cannot move the world (`execStmts_world`), so the next re-read sees
`xs` again. The H2 boundary flip's proof-rebase route rewrites
`execForList` to `execFor` through this and reuses the frozen-tail
induction pattern verbatim. -/
theorem execForList_eq_execFor_snapshot {m : Module} (hm : m.heapFree = true) :
    ∀ (fuel : Nat) (st : FrameState) (target : Expr) (a : Addr) (i : Nat)
      (body : List Stmt) (xs : Array RVal),
      Stmt.heapFreeList body = true →
      Heap.get? st.world.heap a = some (.list xs) →
      execForList m fuel st target a i body
        = execFor m fuel st target (xs.toList.drop i) body
  | 0, st, target, a, i, body, xs, _, _ => by
    simp [execForList, execFor]
  | fuel + 1, st, target, a, i, body, xs, hfree, hget => by
    rw [execForList, execFor.eq_def]
    rw [hget]
    dsimp only
    by_cases hi : i < xs.size
    · have hlen : i < xs.toList.length := by simpa using hi
      rw [if_pos hi, List.drop_eq_getElem_cons hlen]
      simp only [← getD_toList_getElem xs i hi]
      -- equal prefixes (the element bind and the body bind); the
      -- continuations agree on every reachable outcome. Case on the PURE
      -- helper results (never on the `Run` terms — `cases` on them
      -- generalizes `st` out of the context).
      cases hA : assignToH st.world.heap st.locals target (xs.getD i .none) with
      | ok env₁ =>
        rw [Run.liftRes_ok, Run.ok_bind, Run.ok_bind]
        cases hB : execStmts m fuel { st with locals := env₁ } body with
        | ok st₂ flow =>
          rw [Run.ok_bind, Run.ok_bind]
          -- `execStmts_world`'s RHS carries the record-literal state; its
          -- `.world` projection is DEFEQ to `st.world` (exact closes it)
          have hw₂ := execStmts_world hm hfree hB
          cases flow with
          | next =>
            have hget₂ : Heap.get? st₂.world.heap a = some (.list xs) := by
              rw [hw₂]; exact hget
            simpa using execForList_eq_execFor_snapshot hm
              fuel st₂ target a (i + 1) body xs hfree hget₂
          | cont =>
            have hget₂ : Heap.get? st₂.world.heap a = some (.list xs) := by
              rw [hw₂]; exact hget
            simpa using execForList_eq_execFor_snapshot hm
              fuel st₂ target a (i + 1) body xs hfree hget₂
          | brk => rfl
          | ret v => rfl
        | exn st₂ e => rw [Run.exn_bind, Run.exn_bind]
        | timeout => rw [Run.timeout_bind, Run.timeout_bind]
        | unsupported msg => rw [Run.unsupported_bind, Run.unsupported_bind]
      | exn e => rw [Run.liftRes_exn, Run.exn_bind, Run.exn_bind]
      | timeout => rw [Run.liftRes_timeout, Run.timeout_bind, Run.timeout_bind]
      | unsupported msg =>
        rw [Run.liftRes_unsupported, Run.unsupported_bind, Run.unsupported_bind]
    · rw [if_neg hi]
      have hdrop : xs.toList.drop i = [] :=
        List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt hi)
      rw [hdrop]

/-! ## Cross-fuel determinism -/

/-- **Cross-fuel determinism**: two decided (non-`timeout`) results of the
same call, at *any* two fuels, are equal. Fuel is an implementation detail. -/
theorem callFunction_det {m : Module} {fname : String} {args : Array Val}
    {fuel₁ fuel₂ : Nat} {r₁ r₂ : Res Val}
    (h₁ : callFunction m fname args fuel₁ = r₁)
    (h₂ : callFunction m fname args fuel₂ = r₂)
    (hr₁ : r₁ ≠ .timeout) (hr₂ : r₂ ≠ .timeout) : r₁ = r₂ := by
  rcases Nat.le_total fuel₁ fuel₂ with hle | hle
  · exact (callFunction_mono h₁ hr₁ fuel₂ hle).symm.trans h₂
  · exact h₁.symm.trans (callFunction_mono h₂ hr₂ fuel₁ hle)

/-- `CallsTo` is functional: the returned value is unique across all fuels.
The spec-level payoff of `fuelMono`. -/
theorem CallsTo.functional {m : Module} {f : String} {args : Array Val}
    {v w : Val} (hv : CallsTo m f args v) (hw : CallsTo m f args w) : v = w := by
  obtain ⟨fuel₁, h₁⟩ := hv
  obtain ⟨fuel₂, h₂⟩ := hw
  have hd : (.ok v : Res Val) = .ok w :=
    callFunction_det h₁ h₂ (by simp) (by simp)
  exact Res.ok.inj hd

/-- A call cannot both return a value and raise: `==>` and `==>!` are
mutually exclusive (needed for outcome-uniqueness of the `Obs` spine). -/
theorem CallsTo.not_raises {m : Module} {f : String} {args : Array Val}
    {v : Val} {e : PyErr} (hv : CallsTo m f args v)
    (he : ∃ fuel, callFunction m f args fuel = .exn e) : False := by
  obtain ⟨fuel₁, h₁⟩ := hv
  obtain ⟨fuel₂, h₂⟩ := he
  have hd : (.ok v : Res Val) = .exn e :=
    callFunction_det h₁ h₂ (by simp) (by simp)
  cases hd

/-! ## The observation spine (`PyOut` / `Obs`)

The semantic spine of the spec surface (docs/spec-surface.md §10). Fuel
lives *inside* `Obs` and never above it: the decided outcomes
(`returns`/`raises`/`stuck`) assert that *some* fuel decides that way
(fuel monotonicity then makes every larger fuel agree), while `diverges`
asserts that *every* fuel times out. `stuck` (out of the supported tier,
`Res.unsupported`) is deliberately distinct from `diverges` — that
distinction is what keeps specs falsifiable on unsupported programs.

On message-uniqueness of `stuck` (decision, documented): outcomes are
compared *including* the message, because message-uniqueness holds — the
interpreter is a function of fuel, and `callFunction_det` makes any two
decided results (messages and all) equal across fuels. No "up to message"
quotient is needed. -/

/-- Everything a Python call can be observed to do — the outcome alphabet
of the `Obs` judgment. -/
inductive PyOut where
  /-- Terminates normally, returning `v`. -/
  | returns (v : Val)
  /-- Terminates by raising the Python error `e`. -/
  | raises (e : PyErr)
  /-- Never terminates: every fuel times out. -/
  | diverges
  /-- Leaves the supported semantic tier (`Res.unsupported msg`) — loud,
  and distinct from `diverges`. -/
  | stuck (msg : String)
deriving Repr, Inhabited, BEq

/-- The observation judgment: `Obs m f args o` — calling `f` in module `m`
on `args` is observed to do `o`. This is the fuel boundary: no judgment
built on `Obs` mentions fuel again. -/
def Obs (m : Module) (f : String) (args : Array Val) : PyOut → Prop
  | .returns v => ∃ fuel, callFunction m f args fuel = .ok v
  | .raises e => ∃ fuel, callFunction m f args fuel = .exn e
  | .diverges => ∀ fuel, callFunction m f args fuel = .timeout
  | .stuck msg => ∃ fuel, callFunction m f args fuel = .unsupported msg

/-- `returns` is exactly the spec-layer `CallsTo`. -/
@[simp] theorem Obs.returns_iff {m : Module} {f : String} {args : Array Val}
    {v : Val} : Obs m f args (.returns v) ↔ CallsTo m f args v := Iff.rfl

@[simp] theorem Obs.raises_iff {m : Module} {f : String} {args : Array Val}
    {e : PyErr} :
    Obs m f args (.raises e) ↔ ∃ fuel, callFunction m f args fuel = .exn e :=
  Iff.rfl

@[simp] theorem Obs.diverges_iff {m : Module} {f : String} {args : Array Val} :
    Obs m f args .diverges ↔ ∀ fuel, callFunction m f args fuel = .timeout :=
  Iff.rfl

@[simp] theorem Obs.stuck_iff {m : Module} {f : String} {args : Array Val}
    {msg : String} :
    Obs m f args (.stuck msg) ↔
      ∃ fuel, callFunction m f args fuel = .unsupported msg := Iff.rfl

/-- The decided `Res` value an outcome asserts (`diverges ↦ .timeout` — note
the readings differ: `Obs`'s `diverges` is "timeout at *every* fuel").
Injective, which is what reduces `Obs.det` to `callFunction_det`. -/
def PyOut.asRes : PyOut → Res Val
  | .returns v => .ok v
  | .raises e => .exn e
  | .diverges => .timeout
  | .stuck msg => .unsupported msg

theorem PyOut.asRes_inj {o₁ o₂ : PyOut} (h : o₁.asRes = o₂.asRes) : o₁ = o₂ := by
  cases o₁ <;> cases o₂ <;> simp_all [PyOut.asRes]

theorem PyOut.asRes_ne_timeout {o : PyOut} (h : o ≠ .diverges) :
    o.asRes ≠ .timeout := by
  cases o <;> first | exact absurd rfl h | simp [PyOut.asRes]

/-- A non-`diverges` outcome carries a fuel witness deciding exactly its
`asRes` value. -/
theorem Obs.decided {m : Module} {f : String} {args : Array Val} {o : PyOut}
    (h : Obs m f args o) (hd : o ≠ .diverges) :
    ∃ fuel, callFunction m f args fuel = o.asRes := by
  cases o with
  | returns v => exact h
  | raises e => exact h
  | diverges => exact absurd rfl hd
  | stuck msg => exact h

/-- **Outcome determinism**: a call has at most one observable outcome —
values, errors, and stuck *messages* included. Decided-vs-decided is
`callFunction_det` (FuelMono) through the injection `PyOut.asRes`;
decided-vs-`diverges` is a direct contradiction at the deciding fuel. -/
theorem Obs.det {m : Module} {f : String} {args : Array Val} {o₁ o₂ : PyOut}
    (h₁ : Obs m f args o₁) (h₂ : Obs m f args o₂) : o₁ = o₂ := by
  by_cases d₁ : o₁ = .diverges <;> by_cases d₂ : o₂ = .diverges
  · rw [d₁, d₂]
  · -- o₁ diverges but o₂ decides: contradiction at o₂'s fuel.
    subst d₁
    obtain ⟨fuel, hf⟩ := h₂.decided d₂
    exact absurd (hf.symm.trans (Obs.diverges_iff.mp h₁ fuel))
      (PyOut.asRes_ne_timeout d₂)
  · subst d₂
    obtain ⟨fuel, hf⟩ := h₁.decided d₁
    exact absurd (hf.symm.trans (Obs.diverges_iff.mp h₂ fuel))
      (PyOut.asRes_ne_timeout d₁)
  · obtain ⟨fuel₁, hf₁⟩ := h₁.decided d₁
    obtain ⟨fuel₂, hf₂⟩ := h₂.decided d₂
    exact PyOut.asRes_inj (callFunction_det hf₁ hf₂
      (PyOut.asRes_ne_timeout d₁) (PyOut.asRes_ne_timeout d₂))

/-- **Outcome totality** (classical): every call observes *some* outcome —
the four `PyOut` cases partition behaviours. Either every fuel times out
(`diverges`), or some fuel decides, and the decided constructor names the
outcome. -/
theorem Obs.total (m : Module) (f : String) (args : Array Val) :
    ∃ o, Obs m f args o := by
  by_cases h : ∀ fuel, callFunction m f args fuel = .timeout
  · exact ⟨.diverges, h⟩
  · obtain ⟨fuel, hf⟩ := Classical.not_forall.mp h
    cases hr : callFunction m f args fuel with
    | ok v => exact ⟨.returns v, fuel, hr⟩
    | exn e => exact ⟨.raises e, fuel, hr⟩
    | timeout => exact absurd hr hf
    | unsupported msg => exact ⟨.stuck msg, fuel, hr⟩

/-- The outcome of a call is a well-defined denotation: exactly one `PyOut`
observes (`Obs.total` + `Obs.det`; stated explicitly — no Mathlib `∃!`). -/
theorem Obs.existsUnique (m : Module) (f : String) (args : Array Val) :
    ∃ o, Obs m f args o ∧ ∀ o', Obs m f args o' → o' = o := by
  obtain ⟨o, ho⟩ := Obs.total m f args
  exact ⟨o, ho, fun o' ho' => Obs.det ho' ho⟩

end LeanModels.Python
