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
      execFor m fuel st target xs body ⊑ʳ execFor m fuel' st target xs body) := by
  induction fuel with
  | zero =>
    -- Fuel 0 is `.timeout` everywhere, the bottom of `⊑ʳ`.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun m st e fuel' _ => Or.inl (by simp [evalExpr])
    · exact fun m st es fuel' _ => Or.inl (by simp [evalExprs])
    · exact fun m st op e rest fuel' _ => Or.inl (by simp [evalBoolChain])
    · exact fun m st lhs ops cs fuel' _ => Or.inl (by simp [evalCompareChain])
    · exact fun m st s fuel' _ => Or.inl (by simp [execStmt])
    · exact fun m st ss fuel' _ => Or.inl (by simp [execStmts])
    · exact fun m st test body orelse fuel' _ => Or.inl (by simp [execWhile])
    · exact fun m w fname args fuel' _ => Or.inl (by simp [callIn])
    · exact fun m st target xs body fuel' _ => Or.inl (by simp [execFor])
  | succ fuel ih =>
    obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihCall, ihFor⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
                    exact Run.le_bind (ihEs m st cargs.toList k hk) fun _ _ =>
                      Run.le_refl _
                  | none => exact Run.le_refl _
                | none =>
                  -- findFunction → len → sorted → max → min → abs → int →
                  -- NameError/unsupported (each builtin: bind args, result
                  -- fuel-independent)
                  have hb : ∀ {β : Type} (g : FrameState → List RVal → Run FrameState β),
                      (evalExprs m fuel st cargs.toList).bind g ⊑ʳ
                      (evalExprs m k st cargs.toList).bind g :=
                    fun g => Run.le_bind (ihEs m st cargs.toList k hk)
                      fun st vs => Run.le_refl _
                  exact Run.le_ite
                    (Run.le_bind (ihEs m st cargs.toList k hk) fun st vs =>
                      Run.le_withLocals (ihCall m st.world fname vs.toArray k hk))
                    (Run.le_ite (hb _) (Run.le_ite (hb _) (Run.le_ite (hb _)
                      (Run.le_ite (hb _) (Run.le_ite (hb _) (Run.le_ite (hb _)
                        (Run.le_refl _)))))))
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
        | dict keys values _ => simp only [evalExpr]; exact Run.le_refl _
        | «attribute» value attr _ => simp only [evalExpr]; exact Run.le_refl _
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
              Run.le_bind (Run.le_refl _) fun st b =>
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
              exact Run.le_bind (ihE m st value k hk) fun st v =>
                Run.le_bind (Run.le_refl _) fun st env' => Run.le_refl _
            | cons t2 rest2 => exact Run.le_refl _
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
  mono_of_leR ((fuelMono fuel).2.2.2.2.2.2.2.2 m st target xs body fuel' hf) h hr

/-- **Public fuel monotonicity**, derived through the wrapper decomposition
(docs/memory-model.md v2): `callFunction` = thaw ∘ fresh-world ∘ `callIn`
∘ deep-freeze, and thaw/init/freeze are fuel-free — the only fuel is
`callIn`'s, so `callIn_mono` transports the decided public result. -/
theorem callFunction_mono {m : Module} {fname : String} {args : Array Val}
    {fuel : Nat} {r : Res Val} (h : callFunction m fname args fuel = r)
    (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, callFunction m fname args fuel' = r := by
  intro fuel' hf
  unfold callFunction at h ⊢
  rcases (fuelMono fuel).2.2.2.2.2.2.2.1 m (initWorld m) fname
      (args.map RVal.thaw) fuel' hf with hto | heq
  · -- The inner run timed out at `fuel`: then the public result was
    -- `.timeout`, contradicting `hr`.
    rw [hto] at h
    exact absurd h.symm (by simpa using hr)
  · rw [← heq]; exact h

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
