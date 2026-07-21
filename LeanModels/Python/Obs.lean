import LeanModels.Python.Logic

/-!
# Fuel monotonicity and cross-fuel determinism (`LeanModels.Python`)

The enabling theorems for the `Obs` spine (docs/spec-surface.md §10): adding
fuel never changes a decided (non-`timeout`) interpreter result. This is what
makes the fuel parameter a pure implementation detail — any two runs that
decide, at any two fuels, decide identically, so `CallsTo` is functional and
the strengthened partial judgment `~~>` becomes stateable.

Structure:

* `Res.le` (`x ⊑ y`) — the flat approximation order on results: `x` is
  `timeout` or already equals `y`. Fuel-indexed runs form a chain in it.
* `fuelMono` — THE theorem: one conjunction over all eight functions of the
  interpreter's mutual block (`evalExpr`, `evalExprs`, `evalBoolChain`,
  `evalCompareChain`, `execStmt`, `execStmts`, `execWhile`, `callFunction`),
  proved by a single induction on fuel. Each case is symbolic execution of
  one interpreter step, glued by the congruence lemmas `Res.le_bind` /
  `Res.le_ite` (every fuel-free helper is `⊑`-reflexive, every recursive
  call is the induction hypothesis at the decremented fuel).
* `evalExpr_mono` … `callFunction_mono` — the eight per-function corollaries
  in implication form: `F fuel = r → r ≠ .timeout → ∀ fuel' ≥ fuel,
  F fuel' = r`.
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

/-- Flat approximation order on interpreter results: `x ⊑ y` iff `x` is
`timeout` (the run gave up) or `x = y` (the run decided, and `y` agrees).
`fuelMono` shows every interpreter function is monotone in fuel wrt `⊑`. -/
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

/-! ## Fuel monotonicity — the enabling theorem -/

/-- **Fuel monotonicity**, one conjunction over the whole mutual block, by
induction on fuel: for every interpreter function `F` and `fuel ≤ fuel'`,
`F fuel ⊑ F fuel'` — a run that decided keeps its exact result at any higher
fuel. Conjunct order: `evalExpr`, `evalExprs`, `evalBoolChain`,
`evalCompareChain`, `execStmt`, `execStmts`, `execWhile`, `callFunction`
(the order of `Semantics.lean`'s mutual block). Consume it through the
per-function `_mono` corollaries below. -/
theorem fuelMono (fuel : Nat) :
    (∀ (m : Module) (env : Env) (e : Expr) (fuel' : Nat), fuel ≤ fuel' →
      evalExpr m fuel env e ⊑ evalExpr m fuel' env e) ∧
    (∀ (m : Module) (env : Env) (es : List Expr) (fuel' : Nat), fuel ≤ fuel' →
      evalExprs m fuel env es ⊑ evalExprs m fuel' env es) ∧
    (∀ (m : Module) (env : Env) (op : BoolOp) (e : Expr) (rest : List Expr)
        (fuel' : Nat), fuel ≤ fuel' →
      evalBoolChain m fuel env op e rest ⊑ evalBoolChain m fuel' env op e rest) ∧
    (∀ (m : Module) (env : Env) (lhs : Val) (ops : List CmpOp) (cs : List Expr)
        (fuel' : Nat), fuel ≤ fuel' →
      evalCompareChain m fuel env lhs ops cs ⊑ evalCompareChain m fuel' env lhs ops cs) ∧
    (∀ (m : Module) (env : Env) (s : Stmt) (fuel' : Nat), fuel ≤ fuel' →
      execStmt m fuel env s ⊑ execStmt m fuel' env s) ∧
    (∀ (m : Module) (env : Env) (ss : List Stmt) (fuel' : Nat), fuel ≤ fuel' →
      execStmts m fuel env ss ⊑ execStmts m fuel' env ss) ∧
    (∀ (m : Module) (env : Env) (test : Expr) (body orelse : List Stmt)
        (fuel' : Nat), fuel ≤ fuel' →
      execWhile m fuel env test body orelse ⊑ execWhile m fuel' env test body orelse) ∧
    (∀ (m : Module) (fname : String) (args : Array Val) (fuel' : Nat), fuel ≤ fuel' →
      callFunction m fname args fuel ⊑ callFunction m fname args fuel') := by
  induction fuel with
  | zero =>
    -- Fuel 0 is `.timeout` everywhere, the bottom of `⊑`.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun m env e fuel' _ => Or.inl (by simp [evalExpr])
    · exact fun m env es fuel' _ => Or.inl (by simp [evalExprs])
    · exact fun m env op e rest fuel' _ => Or.inl (by simp [evalBoolChain])
    · exact fun m env lhs ops cs fuel' _ => Or.inl (by simp [evalCompareChain])
    · exact fun m env s fuel' _ => Or.inl (by simp [execStmt])
    · exact fun m env ss fuel' _ => Or.inl (by simp [execStmts])
    · exact fun m env test body orelse fuel' _ => Or.inl (by simp [execWhile])
    · exact fun m fname args fuel' _ => Or.inl (by simp [callFunction])
  | succ fuel ih =>
    obtain ⟨ihE, ihEs, ihB, ihC, ihS, ihSs, ihW, ihF⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- evalExpr
    · intro m env e fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases e with
        | constant c _ => simp only [evalExpr]; exact Res.le_refl _
        | name id _ => simp only [evalExpr]; exact Res.le_refl _
        | binOp l op r _ =>
          simp only [evalExpr]
          exact Res.le_bind (ihE m env l k hk) fun a =>
            Res.le_bind (ihE m env r k hk) fun b => Res.le_refl _
        | unaryOp op operand _ =>
          simp only [evalExpr]
          exact Res.le_bind (ihE m env operand k hk) fun v => Res.le_refl _
        | boolOp op values _ =>
          simp only [evalExpr]
          cases values.toList with
          | nil => exact Res.le_refl _
          | cons e0 es => exact ihB m env op e0 es k hk
        | compare l ops comparators _ =>
          simp only [evalExpr]
          exact Res.le_bind (ihE m env l k hk) fun a =>
            ihC m env a ops.toList comparators.toList k hk
        | call cf cargs cu _ =>
          cases cu with
          | some reason => simp only [evalExpr]; exact Res.le_refl _
          | none =>
            cases cf <;> try (simp only [evalExpr]; exact Res.le_refl _)
            case name fname _ =>
              simp only [evalExpr]
              cases Env.lookup env fname with
              | some v =>
                exact Res.le_bind (ihEs m env cargs.toList k hk) fun _ =>
                  Res.le_refl _
              | none =>
                exact Res.le_ite
                  (Res.le_bind (ihEs m env cargs.toList k hk) fun vs =>
                    ihF m fname vs.toArray k hk)
                  (Res.le_ite
                    (Res.le_bind (ihEs m env cargs.toList k hk) fun vs =>
                      Res.le_refl _)
                    (Res.le_refl _))
        | list elts _ =>
          simp only [evalExpr]
          exact Res.le_bind (ihEs m env elts.toList k hk) fun vs => Res.le_refl _
        | tuple elts _ =>
          simp only [evalExpr]
          exact Res.le_bind (ihEs m env elts.toList k hk) fun vs => Res.le_refl _
        | subscript v idx _ =>
          simp only [evalExpr]
          exact Res.le_bind (ihE m env v k hk) fun c =>
            Res.le_bind (ihE m env idx k hk) fun i => Res.le_refl _
        | unsupported pyKind text _ => simp only [evalExpr]; exact Res.le_refl _
    -- evalExprs
    · intro m env es fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases es with
        | nil => simp only [evalExprs]; exact Res.le_refl _
        | cons e rest =>
          simp only [evalExprs]
          exact Res.le_bind (ihE m env e k hk) fun v =>
            Res.le_bind (ihEs m env rest k hk) fun vs => Res.le_refl _
    -- evalBoolChain
    · intro m env op e rest fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        simp only [evalBoolChain]
        refine Res.le_bind (ihE m env e k hk) fun v => ?_
        cases rest with
        | nil => exact Res.le_refl _
        | cons e' rest' =>
          cases op with
          | and => exact Res.le_ite (ihB m env .and e' rest' k hk) (Res.le_refl _)
          | or => exact Res.le_ite (Res.le_refl _) (ihB m env .or e' rest' k hk)
    -- evalCompareChain
    · intro m env lhs ops cs fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases ops with
        | nil =>
          cases cs with
          | nil => simp only [evalCompareChain]; exact Res.le_refl _
          | cons c cs' => simp only [evalCompareChain]; exact Res.le_refl _
        | cons op ops' =>
          cases cs with
          | nil => simp only [evalCompareChain]; exact Res.le_refl _
          | cons e rest =>
            simp only [evalCompareChain]
            exact Res.le_bind (ihE m env e k hk) fun rhs =>
              Res.le_bind (Res.le_refl _) fun b =>
                Res.le_ite (ihC m env rhs ops' rest k hk) (Res.le_refl _)
    -- execStmt
    · intro m env s fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases s with
        | ret value _ =>
          cases value with
          | none => simp only [execStmt]; exact Res.le_refl _
          | some e =>
            simp only [execStmt]
            exact Res.le_bind (ihE m env e k hk) fun v => Res.le_refl _
        | assign targets value _ =>
          simp only [execStmt]
          cases targets.toList with
          | nil => exact Res.le_refl _
          | cons t rest =>
            cases rest with
            | nil =>
              exact Res.le_bind (ihE m env value k hk) fun v =>
                Res.le_bind (Res.le_refl _) fun env' => Res.le_refl _
            | cons t2 rest2 => exact Res.le_refl _
        | augAssign target op value _ =>
          cases target <;> try (simp only [execStmt]; exact Res.le_refl _)
          case name id _ =>
            simp only [execStmt]
            cases Env.lookup env id with
            | none => exact Res.le_refl _
            | some old =>
              cases old <;>
                first
                | exact Res.le_refl _
                | exact Res.le_bind (ihE m env value k hk) fun v =>
                    Res.le_bind (Res.le_refl _) fun r => Res.le_refl _
        | whileLoop test body orelse _ =>
          simp only [execStmt]
          exact ihW m env test body.toList orelse.toList k hk
        | ifStmt test body orelse _ =>
          simp only [execStmt]
          exact Res.le_bind (ihE m env test k hk) fun t =>
            Res.le_ite (ihSs m env body.toList k hk) (ihSs m env orelse.toList k hk)
        | exprStmt e _ =>
          simp only [execStmt]
          exact Res.le_bind (ihE m env e k hk) fun v => Res.le_refl _
        | pass _ => simp only [execStmt]; exact Res.le_refl _
        | brk _ => simp only [execStmt]; exact Res.le_refl _
        | cont _ => simp only [execStmt]; exact Res.le_refl _
        | unsupported pyKind text _ => simp only [execStmt]; exact Res.le_refl _
    -- execStmts
    · intro m env ss fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases ss with
        | nil => simp only [execStmts]; exact Res.le_refl _
        | cons s rest =>
          simp only [execStmts]
          refine Res.le_bind (ihS m env s k hk) fun p => ?_
          obtain ⟨env', flow⟩ := p
          cases flow with
          | next => exact ihSs m env' rest k hk
          | ret v => exact Res.le_refl _
          | brk => exact Res.le_refl _
          | cont => exact Res.le_refl _
    -- execWhile
    · intro m env test body orelse fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        simp only [execWhile]
        refine Res.le_bind (ihE m env test k hk) fun t => ?_
        refine Res.le_ite ?_ (ihSs m env orelse k hk)
        refine Res.le_bind (ihSs m env body k hk) fun p => ?_
        obtain ⟨env', flow⟩ := p
        cases flow with
        | next => exact ihW m env' test body orelse k hk
        | ret v => exact Res.le_refl _
        | brk => exact Res.le_refl _
        | cont => exact ihW m env' test body orelse k hk
    -- callFunction
    · intro m fname args fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        simp only [callFunction]
        cases findFunction m fname with
        | none => exact Res.le_refl _
        | some f =>
          refine Res.le_ite (Res.le_refl _) (Res.le_ite (Res.le_refl _)
            (Res.le_ite (Res.le_refl _) ?_))
          refine Res.le_bind (ihSs m (mkCallEnv f.params args) f.body.toList k hk)
            fun p => ?_
          obtain ⟨env', flow⟩ := p
          cases flow <;> exact Res.le_refl _

/-! ## Per-function corollaries (the `FuelMono` statement shape) -/

private theorem mono_of_le {α : Type} {x y r : Res α}
    (hle : x ⊑ y) (h : x = r) (hr : r ≠ .timeout) : y = r := by
  subst h; exact (Res.le_eq hle hr).symm

/-- Fuel monotonicity for `evalExpr`: a decided result survives any fuel
increase, exactly. -/
theorem evalExpr_mono {m : Module} {fuel : Nat} {env : Env} {e : Expr}
    {r : Res Val} (h : evalExpr m fuel env e = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, evalExpr m fuel' env e = r := fun fuel' hf =>
  mono_of_le ((fuelMono fuel).1 m env e fuel' hf) h hr

/-- Fuel monotonicity for `evalExprs`. -/
theorem evalExprs_mono {m : Module} {fuel : Nat} {env : Env} {es : List Expr}
    {r : Res (List Val)} (h : evalExprs m fuel env es = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, evalExprs m fuel' env es = r := fun fuel' hf =>
  mono_of_le ((fuelMono fuel).2.1 m env es fuel' hf) h hr

/-- Fuel monotonicity for `evalBoolChain`. -/
theorem evalBoolChain_mono {m : Module} {fuel : Nat} {env : Env} {op : BoolOp}
    {e : Expr} {rest : List Expr} {r : Res Val}
    (h : evalBoolChain m fuel env op e rest = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, evalBoolChain m fuel' env op e rest = r := fun fuel' hf =>
  mono_of_le ((fuelMono fuel).2.2.1 m env op e rest fuel' hf) h hr

/-- Fuel monotonicity for `evalCompareChain`. -/
theorem evalCompareChain_mono {m : Module} {fuel : Nat} {env : Env} {lhs : Val}
    {ops : List CmpOp} {cs : List Expr} {r : Res Val}
    (h : evalCompareChain m fuel env lhs ops cs = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, evalCompareChain m fuel' env lhs ops cs = r := fun fuel' hf =>
  mono_of_le ((fuelMono fuel).2.2.2.1 m env lhs ops cs fuel' hf) h hr

/-- Fuel monotonicity for `execStmt`. -/
theorem execStmt_mono {m : Module} {fuel : Nat} {env : Env} {s : Stmt}
    {r : Res (Env × Flow)} (h : execStmt m fuel env s = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, execStmt m fuel' env s = r := fun fuel' hf =>
  mono_of_le ((fuelMono fuel).2.2.2.2.1 m env s fuel' hf) h hr

/-- Fuel monotonicity for `execStmts`. -/
theorem execStmts_mono {m : Module} {fuel : Nat} {env : Env} {ss : List Stmt}
    {r : Res (Env × Flow)} (h : execStmts m fuel env ss = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, execStmts m fuel' env ss = r := fun fuel' hf =>
  mono_of_le ((fuelMono fuel).2.2.2.2.2.1 m env ss fuel' hf) h hr

/-- Fuel monotonicity for `execWhile`. -/
theorem execWhile_mono {m : Module} {fuel : Nat} {env : Env} {test : Expr}
    {body orelse : List Stmt} {r : Res (Env × Flow)}
    (h : execWhile m fuel env test body orelse = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, execWhile m fuel' env test body orelse = r := fun fuel' hf =>
  mono_of_le ((fuelMono fuel).2.2.2.2.2.2.1 m env test body orelse fuel' hf) h hr

/-- Fuel monotonicity for `callFunction`: a decided call result (`ok`, `exn`,
or `unsupported`) is the same at every larger fuel. -/
theorem callFunction_mono {m : Module} {fname : String} {args : Array Val}
    {fuel : Nat} {r : Res Val} (h : callFunction m fname args fuel = r)
    (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, callFunction m fname args fuel' = r := fun fuel' hf =>
  mono_of_le ((fuelMono fuel).2.2.2.2.2.2.2 m fname args fuel' hf) h hr

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
