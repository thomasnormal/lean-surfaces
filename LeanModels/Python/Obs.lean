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
              | dict es v1 =>
                cases o2 with
                | dict fs v2 =>
                  exact Res.le_ite (ihN h ((x, y) :: active) es.toList fs.toList k hk)
                    (Res.le_refl _)
                | list ys => exact Res.le_refl _
                | «instance» ci attrs => exact Res.le_refl _
              | list xs =>
                cases o2 with
                | dict fs v2 => exact Res.le_refl _
                | list ys =>
                  exact Res.le_ite (ihL h ((x, y) :: active) xs.toList ys.toList k hk)
                    (Res.le_refl _)
                | «instance» ci attrs => exact Res.le_refl _
              | «instance» ci attrs => cases o2 <;> exact Res.le_refl _
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
  case inOp =>
    cases b <;> try exact Res.le_refl _
    case ref d => exact heapContains_mono hf
  case notIn =>
    cases b <;> try exact Res.le_refl _
    case ref d =>
      exact Res.le_bind (heapContains_mono hf) fun e => Res.le_refl _

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
      execAttrCall m fuel st a attr args ⊑ʳ execAttrCall m fuel' st a attr args) := by
  induction fuel with
  | zero =>
    -- Fuel 0 is `.timeout` everywhere, the bottom of `⊑ʳ`.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  | succ fuel ih =>
    obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihCall, ihFor, ihItems, ihForL, ihAttrC⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- evalExpr
    · intro m st e fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases e with
        | constant c _ => simp only [evalExpr]; exact Run.le_refl _
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
        | call cf cargs cu _ =>
          cases cu with
          | some reason => simp only [evalExpr]; exact Run.le_refl _
          | none =>
            cases cf <;> try (simp only [evalExpr]; exact Run.le_refl _)
            case «attribute» recv attr spa =>
              -- receiver-first dispatch (H3): the receiver evaluates, then
              -- `execAttrCall` forks on the pure plan (its own conjunct);
              -- an ntuple VALUE receiver (H5) forks on `ntupleCallPlan` —
              -- only the method arm recurses (args + `callIn`)
              simp only [evalExpr]
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
              simp only [evalExpr]
              cases Env.lookup st.locals fname with
              | some v =>
                cases v <;>
                  first
                  | exact Run.le_refl _
                  | exact Run.le_bind (ihEs m st cargs.toList k hk) fun _ _ =>
                      Run.le_refl _
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
                  | none => exact Run.le_refl _
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
                    refine Run.le_ite (Run.le_refl _) ?_
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
                      exact Run.le_ite (hb _) (Run.le_ite (hb _) (Run.le_ite (hb _)
                        (Run.le_ite (hb _) (Run.le_ite (hb _) (Run.le_ite (hb _)
                          (Run.le_refl _))))))
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
            case listV xs => exact ihFor m st target xs.toList body.toList k hk
            case tuple xs => exact ihFor m st target xs.toList body.toList k hk
            case ntuple tn fs xs => exact ihFor m st target xs.toList body.toList k hk
            case ref a => exact ihForL m st target a 0 body.toList k hk
        | ifStmt test body orelse _ =>
          simp only [execStmt]
          exact Run.le_bind (ihE m st test k hk) fun st t =>
            Run.le_bind (Run.le_refl _) fun st b =>
              Run.le_ite (ihSs m st body.toList k hk) (ihSs m st orelse.toList k hk)
        | exprStmt e _ =>
          simp only [execStmt]
          exact Run.le_bind (ihE m st e k hk) fun st v => Run.le_refl _
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
          refine Run.le_ite (Run.le_refl _) (Run.le_ite (Run.le_refl _)
            (Run.le_ite (Run.le_refl _) ?_))
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
        | listAppend =>
          exact Run.le_bind (ihEs m st args k hk) fun st vs => Run.le_refl _
        | listPop =>
          exact Run.le_bind (ihEs m st args k hk) fun st vs => Run.le_refl _
        | refuse msg => exact Run.le_refl _
        | dangling => exact Run.le_refl _

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
  mono_of_leR ((fuelMono fuel).2.2.2.2.2.2.2.2.2.2.2 m st a attr args fuel' hf) h hr

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
    (∀ (st : FrameState) (a : Addr) (args : List Expr),
        Expr.heapFreeList args = true →
      Run.OkW (·.world = st.world) (execAttrCall m fuel st a "get" args)) := by
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
    · intro st a args _ s' a' h; simp [execAttrCall] at h
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
      | name id _ =>
        simp only [evalExpr]
        cases Env.lookup st.locals id with
        | some v => exact .okF rfl _
        | none =>
          cases lookupG (moduleGlobals m).1 id with
          | some vv =>
            cases vv with
            | some v => exact .okF rfl _
            | none => exact .unsupported
          | none =>
            exact .ite .unsupported (.ite .unsupported (.ite .unsupported
              (.ite .unsupported (.ite .exn .unsupported))))
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
      | call cf cargs cu _ =>
        cases cu with
        | some reason => simp only [evalExpr]; exact .unsupported
        | none =>
          cases cf <;> try (simp only [evalExpr]; exact .unsupported)
          case «attribute» recv attr spa =>
            -- the method tier: the FRAGMENT admits exactly `.get` (a heap
            -- read) — hfree pins the attribute, which kills the mutating
            -- `.append`/`.pop` branches; instance receivers dispatch to
            -- classes, and a heap-free module HAS no classes (hm), so the
            -- method branch is vacuous
            simp only [Expr.heapFree, Bool.and_eq_true] at hfree
            have hattr : attr = "get" := by simpa [beq_iff_eq] using hfree.1.1
            subst hattr
            have hrecv : recv.heapFree = true := hfree.1.2
            simp only [evalExpr]
            refine .bind (ihE st recv hrecv) fun st₁ r h₁ => ?_
            cases r <;>
              first
              | exact .unsupported
              | exact ((ihAttrC st₁ _ cargs.toList hfree.2).mono
                  (wtrans st st₁ h₁))
              | skip
            case ntuple tn fs xs =>
              -- heap-free: no classes ⇒ the plan never dispatches
              dsimp only
              rcases ntupleCallPlan_heapFree hm tn fs "get" with hp | ⟨msg, hp⟩ <;>
                rw [hp]
              · exact .exn
              · exact .unsupported
          case name fname _ =>
            -- H2: `sorted` ALLOCATES its result, so the fragment excludes
            -- it (hfree carries `fname != "sorted"` — the branch is
            -- rewritten away before the ite walk)
            simp only [Expr.heapFree, Bool.and_eq_true] at hfree
            have hns : (fname != "sorted") = true := hfree.1
            have hs : (fname == "sorted") = false := by
              cases hbe : fname == "sorted"
              · rfl
              · rw [bne, hbe] at hns; simp at hns
            simp only [evalExpr]
            have hargs : Run.OkW (·.world = st.world) (evalExprs m fuel st cargs.toList) :=
              ihEs st cargs.toList hfree.2
            cases Env.lookup st.locals fname with
            | some v =>
              cases v <;>
                first
                | exact .unsupported
                | exact .bind hargs fun st₁ _ h₁ => .exn
            | none =>
              cases lookupG (moduleGlobals m).1 fname with
              | some vv =>
                cases vv with
                | some v => cases v <;> exact .bind hargs fun st₁ _ h₁ => .exn
                | none => exact .unsupported
              | none =>
                -- a heap-free module has no classes: the instantiation
                -- branch reduces away; the def/namedtuple collision guard
                -- stays an undecided (walked) ite, and namedtuple
                -- CONSTRUCTION is a pure value — world-preserving
                simp only [hs, findClass_heapFree hm fname, Option.isSome_none,
                  Bool.false_or, Bool.false_eq_true, if_false]
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
                    · refine .ite (.bind hargs fun st₁ vs h₁ => .liftResF h₁ _) ?_
                      refine .ite (.bind hargs fun st₁ vs h₁ => .liftResF h₁ _) ?_
                      refine .ite (.bind hargs fun st₁ vs h₁ => ?_) ?_
                      · cases vs with
                        | nil => exact .exn
                        | cons v rest =>
                          cases rest with
                          | nil => exact .liftResF h₁ _
                          | cons _ _ => exact .exn
                      · refine .ite (.bind hargs fun st₁ vs h₁ => ?_)
                          (.ite .unsupported (.ite .exn .unsupported))
                        cases vs with
                        | nil => exact .okF h₁ _
                        | cons v rest =>
                          cases rest with
                          | nil => exact .liftResF h₁ _
                          | cons _ _ => exact .unsupported
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
            all_goals
              exact .bind (ihE st value hfree.2) fun st₁ v h₁ =>
                .bind (.liftResF h₁ _) fun st₂ env' h₂ =>
                  fun _ _ he => by cases he; exact h₂
          | cons t2 rest2 =>
            cases t <;> exact .unsupported
      | augAssign target op value _ =>
        simp only [Stmt.heapFree] at hfree
        cases target <;> try (simp only [execStmt]; exact .unsupported)
        case name id _ =>
          simp only [execStmt]
          cases Env.lookup st.locals id with
          | none => exact .exn
          | some old =>
            cases old <;>
              first
              | exact .unsupported
              | exact .bind (ihE st value hfree) fun st₁ v h₁ =>
                  .bind (.liftResF h₁ _) fun st₂ r h₂ =>
                    fun _ _ he => by cases he; exact h₂
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
          | str s => exact .unsupported
          | listV xs =>
            exact (ihFor st₁ target _ body.toList hfree.1.2).mono
              (wtrans st st₁ h₁)
          | tuple xs =>
            exact (ihFor st₁ target _ body.toList hfree.1.2).mono
              (wtrans st st₁ h₁)
          | ntuple tn fs xs =>
            exact (ihFor st₁ target _ body.toList hfree.1.2).mono
              (wtrans st st₁ h₁)
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
        | dict es ver => exact .unsupported
        | «instance» ci attrs => exact .exn
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
    -- execAttrCall (H3): in a heap-free module the `.get` plan is a heap
    -- READ or a decided refusal (`attrCallPlan_get_heapFree`)
    · intro st a args hargs
      simp only [execAttrCall]
      rcases attrCallPlan_get_heapFree hm st.world.heap a with
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
