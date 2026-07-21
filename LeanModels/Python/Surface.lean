import LeanModels.Python.Logic
import LeanModels.Python.Obs

/-!
# The typed spec surface

Theorems about Python programs should mention neither `Val`, nor fuel, nor
`callFunction` (docs/spec-surface.md). This file provides the first slice of
that surface for the pure tier:

* `Py*` type abbreviations — theorem binders are written against these
  (`PyInt` is definitionally `Int`, documentary today, a migration seam later);
* `ToVal` marshalling, generated-instance style, driven by source annotations
  eventually — hand-listed for the v0 value types here;
* the call judgments: `f(a, b) ==> v` (total: some fuel returns `v`),
  `f(a, b) ⇓ r` (same judgment in hypothesis position, binding a typed
  result for relational specs), `f(a, b) ==>! e` (terminates raising `e`),
  and `f(a, b) ~~> v` — the *strengthened* partial arrow (`PartialTo`):
  every run at every fuel either times out or returns exactly `v`, so a
  terminating outcome can be neither an exception, nor `unsupported`, nor a
  different value. Per the bake-off verdict this is the only admissible
  reading — the weak "if it returns `.ok` then `v`" form is vacuously
  provable on raising/diverging programs and is not offered. Built on the
  `Obs` spine + fuel monotonicity (Obs.lean); connectives at the bottom of
  this file;
* `py_prove` — closes straight-line *and branching* total-correctness goals
  outright; `py_lift` — the house-style opener that turns a `CallsTo`
  induction hypothesis into a fuel-threshold conditional rewrite for
  `simp (disch := omega)` (with `execWhile_at_least` as the loop-lemma
  analog of `CallsTo.at_least`);
* `py_corollary [tot, extras…]` — one-liner for the standard corollaries of
  a total-correctness theorem `tot`: the raw ∀-fuel `@[spec]` form, the
  typed `⇓` form, the `~~>` form, and value-rewritten `==>` restatements
  (`CallsTo.run_eq`/`CallsTo.typed_int_eq`/`CallsTo.partialTo` under the
  hood — every example-file corollary is one `py_corollary` call);
* `execWhile_total_of_invariant` + `py_threshold` — the generic while rule:
  a loop lemma becomes an instantiation (logical state, invariant, step,
  measure) with its two interpreter obligations discharged by threshold
  evaluation at `c + f₀` fuel (`Examples/tri/tri.py`, `Examples/gcd/gcd.py`);
* `#py_check` — non-vacuity checks in surface syntax:
  `#py_check fib(10) = 55` / `#py_check arith.mod(7, 0) raises
  .zeroDivisionError` guard a concrete interpreter run at a fixed generous
  fuel (the smallest-sufficient-fuel `#guard` convention is retired — see
  the docstring);
* spec-side math ops (bottom of file): the `|x|` absolute-value notation and
  the Euclid-step lemmas over `%` (`gcd_emod_step`/`gcd_fmod_step`) that the
  gallery statements need but core Lean does not provide.
-/

namespace LeanModels.Python

/-! ## Py-branded types (spec-surface discipline) -/

/-- Python `int` — exactly mathematical `Int`. -/
abbrev PyInt := Int
/-- Python `bool`. -/
abbrev PyBool := Bool
/-- Python `str` (caveat lector: CPython admits lone surrogates; a faithful
distinct type may replace this abbreviation later). -/
abbrev PyStr := String

/-! ## Marshalling -/

/-- Lean-value → `Val` injection, the typed-wrapper boundary. Marshalling is
always exact; mathematical types appear only inside spec propositions. -/
class ToVal (α : Type) where
  toVal : α → Val

instance : ToVal Val := ⟨id⟩
instance : ToVal Int := ⟨.int⟩
instance : ToVal Nat := ⟨fun n => .int n⟩
instance : ToVal Bool := ⟨.bool⟩
instance : ToVal String := ⟨.str⟩
instance {α} [ToVal α] : ToVal (List α) :=
  ⟨fun xs => .list (xs.map ToVal.toVal).toArray⟩

@[simp] theorem toVal_val (v : Val) : (ToVal.toVal v : Val) = v := rfl
@[simp] theorem toVal_int (n : Int) : (ToVal.toVal n : Val) = .int n := rfl
@[simp] theorem toVal_nat (n : Nat) : (ToVal.toVal n : Val) = .int n := rfl
@[simp] theorem toVal_bool (b : Bool) : (ToVal.toVal b : Val) = .bool b := rfl
@[simp] theorem toVal_str (s : String) : (ToVal.toVal s : Val) = .str s := rfl
@[simp] theorem toVal_list {α} [ToVal α] (xs : List α) :
    (ToVal.toVal xs : Val) = .list (xs.map ToVal.toVal).toArray := rfl

/-! ## Judgments -/

/-- Terminates raising `e` (the `==>!` arrow). `CallsTo` (Logic.lean) is the
`==>`/`⇓` target. -/
def Raises (m : Module) (f : String) (args : Array Val) (e : PyErr) : Prop :=
  ∃ fuel, callFunction m f args fuel = .exn e

/-- `==>!` is exactly the `raises` outcome of the `Obs` spine. -/
theorem Raises.obs_iff {m : Module} {f : String} {args : Array Val} {e : PyErr} :
    Raises m f args e ↔ Obs m f args (.raises e) := Iff.rfl

/-- The **strengthened partial judgment** (target of the `~~>` arrow): every
run, at every fuel, either times out or returns exactly `v` — a terminating
outcome can be neither an exception, nor `unsupported`, nor a different
value. On the `Obs` spine: the only observable outcomes are `returns v` and
`diverges` (`PartialTo.iff_obs`). It does NOT assert termination
(`PartialTo.of_diverges` — any `v` is a `~~>`-spec of a diverging call);
pair with termination evidence to upgrade to `==>` (`PartialTo.callsTo`). -/
def PartialTo (m : Module) (f : String) (args : Array Val) (v : Val) : Prop :=
  ∀ fuel r, callFunction m f args fuel = r → r = .timeout ∨ r = .ok v

theorem CallsTo.intro {m : Module} {f : String} {args : Array Val} {v : Val}
    (fuel : Nat) (h : callFunction m f args fuel = .ok v) :
    CallsTo m f args v := ⟨fuel, h⟩

theorem CallsTo.elim {m f args v} (h : CallsTo m f args v) :
    ∃ fuel, callFunction m f args fuel = .ok v := h

/-- Fuel-threshold form of a `CallsTo` fact: the run succeeds at *every*
sufficiently large fuel. Destructure with `obtain ⟨f₀, h⟩ := hc.at_least`; the
resulting `h : ∀ F, f₀ ≤ F → callFunction … F = .ok v` is a *conditional
rewrite rule* — `simp (disch := omega) only [h]` closes recursive call sites
at whatever fuel the symbolic execution produced, with no exact-offset
bookkeeping (no `max f₁ f₂ + 3`-style coupling to interpreter step counts). -/
theorem CallsTo.at_least {m f args v} (h : CallsTo m f args v) :
    ∃ f₀, ∀ F, f₀ ≤ F → callFunction m f args F = .ok v := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, fun F hF => callFunction_mono hf (by simp) F hF⟩

/-- Fuel-threshold form of a completed `execWhile` run — the loop analog of
`CallsTo.at_least`, consuming exactly what a loop lemma's induction
hypothesis provides (`∃ fuel, execWhile … = .ok (env', flow)`). The
resulting `h : ∀ F, f₀ ≤ F → execWhile … F … = .ok p` is a *conditional
rewrite rule*: after one `rw [execWhile.eq_2]; py_simp […]` body step,
`simp (disch := omega) only [h]` closes the frozen loop occurrence at
whatever fuel the symbolic execution produced (`Examples/tri/tri.py`) —
no exact-offset fuel bookkeeping. Caveat: when the loop lemma was applied at
metavariable spans (module- and span-agnostic lemmas instantiated with `_`),
`simp` cannot index `h`; splice it with the conditional `rw [h]` instead and
discharge the `f₀ ≤ F` side goal by `omega` (see `tri_total`). -/
theorem execWhile_at_least {m : Module} {env : Env} {test : Expr}
    {body orelse : List Stmt} {p : Env × Flow}
    (h : ∃ fuel, execWhile m fuel env test body orelse = .ok p) :
    ∃ f₀, ∀ F, f₀ ≤ F → execWhile m F env test body orelse = .ok p := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, fun F hF => execWhile_mono hf (by simp) F hF⟩

/-! ## The generic while rule -/

/-- **The generic total-correctness while rule.** Instantiate with a logical
state `σ`, its rendering `toEnv` into interpreter environments, an invariant,
a boolean continuation condition (the truthiness of the loop test), the body's
logical effect `step`, and a decreasing measure. The conclusion: from any
invariant state, *some* fuel runs the loop to completion, landing in an
invariant state where the test is false. All fuel bookkeeping is internal —
a loop lemma becomes pure invariant/measure mathematics plus two symbolic
executions (`Examples/tri/tri.py`, `Examples/gcd/gcd.py`).

v1 restrictions (deliberate; they match every loop in the gallery so far):
the `orelse` block is `[]`, and on every invariant-and-continuing state the
body must land in `.next` flow — no `break`/`continue`/`return` escape
routes (those want extra exit conclusions; add them when a gallery program
needs one).

Discharging `htest`/`hbody` — the threshold-eval recipe: both ask for a run
of straight-line code at *every* fuel `F ≥ f₀`. Pick a generous constant
`f₀`, then `intro F hF; obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hF;
rw [Nat.add_comm]` — the fuel is now literally `c + f₀`, whose successor
shape lets `py_simp` execute step by step while the tail fuel `c` stays
symbolic. The `py_threshold` tactic below packages exactly this recipe.
Instantiation caveat: pass `test`, `body` (and `σ` where inference needs
it) explicitly — left as `_` they stay metavariables inside the obligation
goals, and symbolic execution cannot run on an unknown AST. -/
theorem execWhile_total_of_invariant {σ : Type}
    (m : Module) (test : Expr) (body : List Stmt)
    (toEnv : σ → Env) (Inv : σ → Prop) (Cont : σ → Bool)
    (step : σ → σ) (μ : σ → Nat) (tv : σ → Val)
    (htest : ∀ s, Inv s →
      ∃ f₀, ∀ F, f₀ ≤ F → evalExpr m F (toEnv s) test = .ok (tv s))
    (htv : ∀ s, Inv s → truthy (tv s) = Cont s)
    (hbody : ∀ s, Inv s → Cont s = true →
      ∃ f₀, ∀ F, f₀ ≤ F →
        execStmts m F (toEnv s) body = .ok (toEnv (step s), .next))
    (hinv : ∀ s, Inv s → Cont s = true → Inv (step s))
    (hdec : ∀ s, Inv s → Cont s = true → μ (step s) < μ s) :
    ∀ s, Inv s →
      ∃ s', Inv s' ∧ Cont s' = false ∧
        ∃ F, execWhile m F (toEnv s) test body [] = .ok (toEnv s', .next) := by
  intro s hs
  generalize hμ : μ s = n
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    obtain ⟨ft, hft⟩ := htest s hs
    by_cases hc : Cont s = true
    · -- loop iterates: run body, then the recursion at the smaller measure
      obtain ⟨fb, hfb⟩ := hbody s hs hc
      obtain ⟨s', hs', hc', F, hF⟩ :=
        ih (μ (step s)) (hμ ▸ hdec s hs hc) (step s) (hinv s hs hc) rfl
      have hF' := execWhile_mono hF (by simp)
      refine ⟨s', hs', hc', ft + fb + F + 1, ?_⟩
      rw [execWhile]
      rw [hft (ft + fb + F) (by omega)]
      simp only [Res.ok_bind]
      rw [htv s hs, hc]
      simp only [if_true]
      rw [hfb (ft + fb + F) (by omega)]
      simp only [Res.ok_bind]
      exact hF' (ft + fb + F) (by omega)
    · -- test is false: exit immediately (orelse = [] finishes in one step)
      have hcf : Cont s = false := by revert hc; cases Cont s <;> simp
      refine ⟨s, hs, hcf, ft + 2, ?_⟩
      rw [execWhile]
      rw [hft (ft + 1) (by omega)]
      simp only [Res.ok_bind]
      rw [htv s hs]
      simp [hcf, execStmts]

open Lean Lean.Parser.Tactic in
/-- `py_threshold f₀ [extras]` — discharge a fuel-threshold obligation
`∃ f₀, ∀ F, f₀ ≤ F → <interpreter run> = .ok v` for straight-line code (the
`htest`/`hbody` obligations of `execWhile_total_of_invariant`): commits to
the threshold `f₀` (any generous constant ≥ the code's step count works),
rewrites the fuel to `c + f₀` (`Nat.exists_eq_add_of_le` + `Nat.add_comm` —
the literal offset is what lets `py_simp`'s equations fire while the tail
fuel `c` stays symbolic), symbolically executes with `py_simp [extras]`, and
mops up a residual symbolic branch with `split <;> simp_all` (e.g. a
comparison that executed to `if i ≤ n then .ok (.bool true) else …` against
the spec-side `.ok (.bool (decide (i ≤ n)))`). Pass facts the execution
needs as `extras` — e.g. the divisor-nonzero hypothesis that decides `%`'s
`ZeroDivisionError` guard (`Examples/gcd/gcd.py`). -/
macro (name := pyThresholdTactic) "py_threshold" k:num
    "[" args:(simpStar <|> simpErase <|> simpLemma),* "]" : tactic => do
  let extra : Syntax.TSepArray
      [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
       `Lean.Parser.Tactic.simpLemma] "," := ⟨args.elemsAndSeps⟩
  `(tactic|
    (refine ⟨$k, fun F hF => ?_⟩
     obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hF
     subst hc
     rw [Nat.add_comm]
     py_simp [$extra,*]
     try (split <;> simp_all)))

@[inherit_doc pyThresholdTactic]
macro "py_threshold" k:num : tactic => `(tactic| py_threshold $k [])

/-! ## The arrows

`fib(n) ==> v` — the identifier is both the loaded module constant and the
function name; a dotted identifier `arith.floordiv(a, b)` splits into module
`arith`, function `"floordiv"`. Preconditions stay ordinary hypotheses. -/

syntax:50 term:max noWs "(" term,* ")" " ==> " term:51 : term
syntax:50 term:max noWs "(" term,* ")" " ⇓ " term:51 : term
syntax:50 term:max noWs "(" term,* ")" " ==>! " term:51 : term
syntax:50 term:max noWs "(" term,* ")" " ~~> " term:51 : term

open Lean in
/-- Split a (possibly dotted) surface identifier into the module constant and
the Python function-name string literal. -/
private def splitCallee (f : TSyntax `ident) : MacroM (TSyntax `ident × StrLit) := do
  let n := f.getId
  match n with
  | .str p s =>
    let modName := if p.isAnonymous then n else p
    return (mkIdentFrom f modName, Syntax.mkStrLit s)
  | _ => Macro.throwErrorAt f "expected a (possibly dotted) function identifier"

macro_rules
  | `($f:ident($args,*) ==> $v) => do
      let (m, s) ← splitCallee f
      let vs ← args.getElems.mapM fun a => `(ToVal.toVal $a)
      `(CallsTo $m $s #[$vs,*] (ToVal.toVal $v))
  | `($f:ident($args,*) ⇓ $r) => do
      let (m, s) ← splitCallee f
      let vs ← args.getElems.mapM fun a => `(ToVal.toVal $a)
      `(CallsTo $m $s #[$vs,*] (ToVal.toVal $r))
  | `($f:ident($args,*) ==>! $e) => do
      let (m, s) ← splitCallee f
      let vs ← args.getElems.mapM fun a => `(ToVal.toVal $a)
      `(Raises $m $s #[$vs,*] ($e : PyErr))
  | `($f:ident($args,*) ~~> $v) => do
      let (m, s) ← splitCallee f
      let vs ← args.getElems.mapM fun a => `(ToVal.toVal $a)
      `(PartialTo $m $s #[$vs,*] (ToVal.toVal $v))

/-- `#py_check f(args…) = v` / `#py_check f(args…) raises e` — non-vacuity
checks in surface syntax. The command expands to a `#guard` of one concrete
interpreter run at a fixed generous fuel (4096 — concrete runs cost time
proportional to actual steps, not to fuel, so generosity is free) against
`.ok (toVal v)`, resp. `.exn e`. Callees split exactly as the arrows do
(`#py_check arith.mod(7, 0) raises .zeroDivisionError`).

Convention (recorded here): example files state every value- or
exception-shaped non-vacuity check with `#py_check`; the earlier
smallest-sufficient-fuel `#guard` convention is retired — fuel is
existential in every judgment, so a minimal fuel documented nothing any
theorem consumes, while coupling the examples to interpreter step counts.
Raw `#guard` remains only for checks the surface form cannot express
(`matches .unsupported`, spec-side math facts). -/
syntax (name := pyCheckCmd) "#py_check " term:max noWs "(" term,* ")" " = " term : command

@[inherit_doc pyCheckCmd]
syntax (name := pyCheckRaisesCmd)
  "#py_check " term:max noWs "(" term,* ")" &" raises " term : command

macro_rules
  | `(#py_check $f:ident($args,*) = $v) => do
      let (m, s) ← splitCallee f
      let vs ← args.getElems.mapM fun a => `(ToVal.toVal $a)
      `(#guard callFunction $m $s #[$vs,*] 4096 == .ok (ToVal.toVal $v))
  | `(#py_check $f:ident($args,*) raises $e) => do
      let (m, s) ← splitCallee f
      let vs ← args.getElems.mapM fun a => `(ToVal.toVal $a)
      `(#guard callFunction $m $s #[$vs,*] 4096 == .exn ($e : PyErr))

/-! ## `~~>` connectives

The truth table of the arrows, each entry proved below. Note the task-sheet
guess that `==> v → ~~> v` fails is **wrong for this semantics**: the
interpreter is deterministic modulo fuel (`callFunction_det`, i.e.
FuelMono), so one decided run forces every other decided run — at any fuel
— to agree, and totality *subsumes* the strengthened partial judgment.

* `CallsTo.partialTo` — `f(x) ==> v → f(x) ~~> v` (via FuelMono).
* `PartialTo.callsTo` — `~~>` upgrades back to `==>` given any termination
  evidence. The unconditioned converse `~~> v → ==> v` is FALSE in
  general: `PartialTo.of_diverges` exhibits every `v` as a `~~>`-spec of an
  always-diverging call (which is why `~~>` needs no termination argument).
* `CallsTo.eq_of_partialTo` — agreement, `f(x) ==> v ∧ f(x) ~~> w → v = w`
  (needs no monotonicity: one shared fuel suffices).
* `PartialTo.not_raises` — `~~>` is inconsistent with `==>!` (and with a
  `stuck` outcome, via `PartialTo.iff_obs`): the strengthened reading is
  falsifiable on raising programs, unlike the naive one.
* `PartialTo.iff_obs` — the `Obs`-spine characterization: `f(x) ~~> v` iff
  the only observable outcomes are `returns v` and `diverges`.
-/

/-- Total implies strengthened partial: `f(x) ==> v → f(x) ~~> v`. Holds
because the semantics is deterministic modulo fuel — any decided run must
agree with the `.ok v` witness (`callFunction_det`/FuelMono). -/
theorem CallsTo.partialTo {m : Module} {f : String} {args : Array Val}
    {v : Val} (h : CallsTo m f args v) : PartialTo m f args v := by
  obtain ⟨fuel₀, h₀⟩ := h
  intro fuel r hr
  by_cases ht : r = .timeout
  · exact Or.inl ht
  · exact Or.inr (callFunction_det hr h₀ ht (by simp))

/-- Strengthened partial + any termination evidence = total. (The
termination hypothesis is the constructive `∃ fuel`-decides form;
classically it is `¬ Obs m f args .diverges` by `Obs.total`/`Obs.det`.) -/
theorem PartialTo.callsTo {m : Module} {f : String} {args : Array Val}
    {v : Val} (h : PartialTo m f args v)
    (ht : ∃ fuel, callFunction m f args fuel ≠ .timeout) :
    CallsTo m f args v := by
  obtain ⟨fuel, hne⟩ := ht
  rcases h fuel _ rfl with hto | hok
  · exact absurd hto hne
  · exact ⟨fuel, hok⟩

/-- `~~>` alone never proves termination: *every* value is a
strengthened-partial result of an always-diverging call. (This is the
counterexample schema showing `~~> v → ==> v` cannot hold.) -/
theorem PartialTo.of_diverges {m : Module} {f : String} {args : Array Val}
    (h : Obs m f args .diverges) (v : Val) : PartialTo m f args v := by
  intro fuel r hr
  exact Or.inl (hr.symm.trans (Obs.diverges_iff.mp h fuel))

/-- Agreement: a total result and a strengthened-partial spec value
coincide. Needs no fuel monotonicity — instantiating `~~>` at the `==>`
witness fuel suffices. -/
theorem CallsTo.eq_of_partialTo {m : Module} {f : String} {args : Array Val}
    {v w : Val} (hv : CallsTo m f args v) (hw : PartialTo m f args w) :
    v = w := by
  obtain ⟨fuel, h⟩ := hv
  rcases hw fuel _ h with ht | hok
  · cases ht
  · exact Res.ok.inj hok

/-- `~~>` rules exceptions out entirely: it is inconsistent with `==>!`.
This is exactly what the naive "if it returns then `v`" reading fails to
provide. -/
theorem PartialTo.not_raises {m : Module} {f : String} {args : Array Val}
    {v : Val} {e : PyErr} (h : PartialTo m f args v)
    (he : Raises m f args e) : False := by
  obtain ⟨fuel, hf⟩ := he
  rcases h fuel _ hf with ht | hok
  · cases ht
  · cases hok

/-- The `Obs`-spine reading of the strengthened partial arrow:
`f(x) ~~> v` iff `returns v` and `diverges` are the only observable
outcomes — no `raises`, no `stuck`, no other value. -/
theorem PartialTo.iff_obs {m : Module} {f : String} {args : Array Val}
    {v : Val} :
    PartialTo m f args v ↔
      ∀ o, Obs m f args o → o = .returns v ∨ o = .diverges := by
  constructor
  · intro h o ho
    cases o with
    | returns w =>
      obtain ⟨fuel, hf⟩ := ho
      rcases h fuel _ hf with ht | hok
      · cases ht
      · exact Or.inl (by rw [Res.ok.inj hok])
    | raises e =>
      obtain ⟨fuel, hf⟩ := ho
      rcases h fuel _ hf with ht | hok
      · cases ht
      · cases hok
    | diverges => exact Or.inr rfl
    | stuck msg =>
      obtain ⟨fuel, hf⟩ := ho
      rcases h fuel _ hf with ht | hok
      · cases ht
      · cases hok
  · intro h fuel r hf
    cases r with
    | ok w =>
      rcases h (.returns w) ⟨fuel, hf⟩ with he | he
      · exact Or.inr (by rw [PyOut.returns.inj he])
      · cases he
    | exn e =>
      rcases h (.raises e) ⟨fuel, hf⟩ with he | he
      · cases he
      · cases he
    | timeout => exact Or.inl rfl
    | unsupported msg =>
      rcases h (.stuck msg) ⟨fuel, hf⟩ with he | he
      · cases he
      · cases he

/-! ## `py_lift` and `py_prove` -/

open Lean Lean.Parser.Tactic in
/-- `py_lift ⟨f₀, h⟩ := e with [prog]` — the house-style opener for splicing
a recursive run into a symbolic execution (`Examples/fib/fib.py`): `e` is
any `CallsTo` fact (typically the induction hypothesis at a smaller
argument); the macro takes its fuel-threshold form (`CallsTo.at_least`) and
symbolically normalizes it, binding the threshold `f₀` and
`h : ∀ F, f₀ ≤ F → callFunction ⟨…⟩ … F = .ok v` with the program literal
`prog` unfolded. `h` is a *conditional rewrite rule*: after executing the
enclosing body (`rw [callFunction.eq_2]; py_simp […]`), close the frozen
recursive call sites with `simp (disch := omega) only [h]` — `omega`
discharges the `f₀ ≤ F` side conditions at whatever fuel the execution
produced, so no exact-offset fuel bookkeeping ever appears (pick any
generous slack for the outer witness). Implementation note: the unfold and
the normalization are one fused `py_simp [prog] at h` — the two-step
`simp only [prog] at h; py_simp at h` form fails with "no progress" on
hypotheses that need no cast normalization. -/
macro "py_lift" "⟨" fid:ident "," hid:ident "⟩" " := " e:term " with "
    "[" args:(simpStar <|> simpErase <|> simpLemma),* "]" : tactic => do
  let extra : Syntax.TSepArray
      [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
       `Lean.Parser.Tactic.simpLemma] "," := ⟨args.elemsAndSeps⟩
  `(tactic|
    (obtain ⟨$fid, $hid⟩ := ($e).at_least
     py_simp [$extra,*] at $hid:ident))

open Lean Lean.Parser.Tactic in
/-- `py_prove [prog, extra…]` closes total-correctness goals (`f(a, b) ==> v`,
`f(a) ==>! e`) for straight-line *and branching* loop-free bodies: it
supplies a fuel witness (32 — ample for loop-free bodies), symbolically
executes the interpreter with `py_simp` (pass the loaded program literal,
e.g. `py_prove [add]`), and discharges residual value equations with
`rfl`/`omega`. A symbolic branch (`if x < 0:`) survives execution as an
`ite` inside the existential nest; the branch-splitting attempt case-splits
it with `split` (which reaches under the `∃` binders — `split_ifs` does not
exist on this toolchain), re-executes each arm with `py_simp`, and finishes
with `omega`, so `Examples/my_abs/my_abs.py`'s `my_abs(x) ==> |x|` closes by
bare `py_prove [my_abs]`. Attempt order is load-bearing: the all-tactic
attempts come first and are guarded by `done`, because an `exact … (by …)`
alternative *commits* inside `first` even when its nested `by` block fails
(the failure is recovered with `sorry` and merely logged) — a fallback
placed after it would be unreachable. Loops and recursion still need their
invariant/induction lemmas (see `py_lift` / `execWhile_at_least`) — that
automation arrives with the bridge layer; `py_prove` is the front door that
grows, not a promise it keeps yet. -/
macro "py_prove" "[" args:(simpStar <|> simpErase <|> simpLemma),* "]" : tactic => do
  let extra : Syntax.TSepArray
      [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
       `Lean.Parser.Tactic.simpLemma] "," := ⟨args.elemsAndSeps⟩
  `(tactic|
    (intros
     first
       | (refine ⟨32, ?_⟩
          py_simp [callFunction, $extra,*]
          first
            | done
            | split <;> py_simp <;> omega
            | omega
          done)
       | exact CallsTo.intro 32 (by py_simp [callFunction, $extra,*])
       | refine ⟨32, ?_⟩ <;> py_simp [callFunction, $extra,*]
       | (py_simp [callFunction, $extra,*]
          all_goals try (first | rfl | omega))))

/-! ## `py_corollary` — the standard corollaries, one call each

Every total-correctness theorem spawns the same family of corollaries
(determinism modulo fuel does all the work): the raw ∀-fuel `@[spec]` form
(`callFunction … fuel = .ok r → r = v`), the typed `⇓` form (`f(n) ⇓ r →
r = e`), the strengthened-partial `~~>` form, and occasionally a
value-rewritten `==>` restatement. `py_corollary [tot]` closes any of them
from the total theorem alone — the two curried determinism lemmas below are
its `refine` heads (the run/`⇓` hypothesis is found by `assumption`, the
`CallsTo` obligation becomes the goal and is closed by `apply tot`). -/

/-- Determinism against a concrete run, curried for `py_corollary`: a `.ok`
result at any fuel equals the value of any `CallsTo` fact — the conclusion
shape of the raw ∀-fuel `@[spec]` corollaries (`CallsTo.functional`, i.e.
FuelMono). -/
theorem CallsTo.run_eq {m : Module} {f : String} {args : Array Val}
    {fuel : Nat} {r v : Val} (h : callFunction m f args fuel = .ok r)
    (ht : CallsTo m f args v) : r = v :=
  CallsTo.functional ⟨fuel, h⟩ ht

/-- Determinism on the typed surface, curried for `py_corollary`: an
`Int`-marshalled `⇓`-bound result equals the `Int` value of any `CallsTo`
fact (`Val.int.inj` peels the marshalling) — the conclusion shape of the
typed corollaries. -/
theorem CallsTo.typed_int_eq {m : Module} {f : String} {args : Array Val}
    {r e : Int} (h : CallsTo m f args (.int r))
    (ht : CallsTo m f args (.int e)) : r = e :=
  Val.int.inj (CallsTo.functional h ht)

open Lean Lean.Parser.Tactic in
/-- `py_corollary [tot, extras…]` — close a standard corollary of the
total-correctness theorem `tot` (any `==>`/`⇓` fact, optionally already
instantiated, e.g. `py_corollary [fib_total n.toNat]`). Handles all four
gallery corollary shapes:

* raw ∀-fuel `@[spec]` form — `h : callFunction m f args fuel = .ok r ⊢
  r = v` (via `CallsTo.run_eq`);
* typed `⇓` form — `h : f(n) ⇓ r ⊢ r = e` (via `CallsTo.typed_int_eq`);
* strengthened partial — `⊢ f(n) ~~> v` (via `CallsTo.partialTo`);
* value-rewritten `==>` restatement — `⊢ f(n) ==> v'` with `v'` a
  propositionally (not definitionally) equal value.

After the `refine` head, the `CallsTo` obligation is closed by applying
`tot` with side hypotheses (`0 ≤ n`, …) discharged by `assumption`; when
plain unification cannot bridge the value forms, the fallback normalizes
`tot`'s statement with `simp (disch := omega) only [toVal_*, extras…]` and
retries — `extras` are additional rewrites for that bridge
(`Int.fdiv_eq_ediv_of_nonneg` for `midpoint_nonneg`; `Int.toNat_of_nonneg`,
the Nat/Int marshalling bridge of `fib_spec`, is always included). -/
macro (name := pyCorollaryTactic) "py_corollary" "[" tot:term ","
    args:(simpStar <|> simpErase <|> simpLemma),* "]" : tactic => do
  let extra : Syntax.TSepArray
      [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
       `Lean.Parser.Tactic.simpLemma] "," := ⟨args.elemsAndSeps⟩
  `(tactic|
    (intros
     first
       | refine CallsTo.partialTo ?_
       | refine CallsTo.run_eq ‹_› ?_
       | refine CallsTo.typed_int_eq ‹_› ?_
       | skip
     first
       | exact $tot
       | (apply $tot <;> assumption)
       | (have ht := $tot
          set_option linter.unusedSimpArgs false in
          simp (disch := omega) only [toVal_int, toVal_nat, toVal_bool,
            toVal_str, toVal_list, toVal_val, $extra,*] at ht
          first | exact ht | (apply ht <;> assumption))))

@[inherit_doc pyCorollaryTactic]
macro "py_corollary" "[" tot:term "]" : tactic =>
  `(tactic| py_corollary [$tot, Int.toNat_of_nonneg])

/-! ## The three-file example layout: the `proofs` tactic

Per-example directories `Examples/<name>/` split an example into
`spec.lean` — `load_program`, `#py_check` lines, docstrings, and theorem
*statements*, each proved `:= by proofs` — and `proof.lean`, the real
proofs, wrapped in a namespace equal to its module path
(`namespace Examples.<name>.proof`) and imported by the spec
(`import Examples.<name>.proof`). Lean has no forward declarations, so the
statement is duplicated in both files BY DESIGN; the `:= by proofs`
reference is what typechecks the duplication — a drifted statement fails to
close. Each file runs its own `load_program`, so the two program constants
are distinct names for the same literal `Module`; unification bridges them
by unfolding. -/

open Lean Elab Tactic in
/-- `proofs` — close a spec-file theorem with its proof-file twin. Reads the
current declaration's name (e.g. `tri_total`) and the current module name
(e.g. `Examples.tri.spec`), rewrites the module's last component `spec` →
`proof`, resolves `<proof-module-namespace>.<decl-name>`
(`Examples.tri.proof.tri_total`), and closes the goal with
`first | exact thm | (apply thm <;> assumption)` — `exact` when the proof
theorem's remaining shape matches outright, `apply … <;> assumption` to
instantiate binders against the goal and discharge side hypotheses
(`0 ≤ n`, a `⇓`/run hypothesis, …) from the local context. Missing twin,
wrong module shape, and use outside a declaration are precise errors. -/
elab "proofs" : tactic => do
  let some declName ← Term.getDeclName?
    | throwError "proofs: no enclosing declaration — `proofs` only makes sense as a theorem's proof (`:= by proofs`)"
  let mod ← getMainModule
  let .str modPre "spec" := mod
    | throwError "proofs: current module `{mod}` is not an `<example>.spec` module — `proofs` pairs `….spec` with its sibling `….proof` (see the three-file layout note above its definition)"
  let proofNs := Name.str modPre "proof"
  let target := proofNs ++ declName
  unless (← getEnv).contains target do
    throwError "no proof named {declName} in {proofNs} — add it to proof.lean"
  let thm := mkCIdent target
  evalTactic (← `(tactic| first
    | exact $thm
    | (apply $thm <;> assumption)))

/-! ## Spec-side math ops

Reusable helpers for stating gallery specs in *mathematical* Lean
(docs/spec-surface.md): core Lean v4.33 has no `abs`/`|·|` on `Int` and no
`Int.gcd` recursion lemma over `%`, so the spec surface provides the missing
pieces in their Python-shaped forms (Python's `%` is `Int.fmod`). -/

/-- `|x|` — spec-side absolute value on `PyInt` (gallery example 1,
`my_abs(x) ==> |x|`). Core Lean has no `abs`, so this elaborates to
`Int.natAbs` cast back to `Int`, which `omega` handles natively — goals
mentioning `|x|` need no unfolding step. v0: `Int`-valued only (the float
tier will want its own). -/
scoped macro:max (name := specAbsNotation) atomic("|" noWs) x:term noWs "|" : term =>
  `(((Int.natAbs $x : Nat) : Int))

/-- Euclid's step over Lean's `%` (`Int.emod`): `Nat.gcd_rec` transported
through `natAbs` (`Int.natAbs_emod_of_nonneg`). Only the dividend needs a
sign hypothesis — the identity holds for every divisor, zero included. -/
theorem gcd_emod_step {a : Int} (ha : 0 ≤ a) (b : Int) :
    Int.gcd b (a % b) = Int.gcd a b := by
  rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.gcd_eq_natAbs_gcd_natAbs,
      Int.natAbs_emod_of_nonneg ha,
      Nat.gcd_comm b.natAbs, ← Nat.gcd_rec, Nat.gcd_comm]

/-- Euclid's step over Python's `%` (`Int.fmod`, `evalBinOp`'s `.mod`): on a
nonnegative divisor `fmod` coincides with `%`
(`Int.fmod_eq_emod_of_nonneg`), so this is `gcd_emod_step` in the exact
shape the interpreter emits — the invariant-preservation step of
`Examples/gcd/gcd.py`'s `gcd_total`. The sign hypotheses
are not decoration: `Int.gcd 4 (-6) = 2` but `(4).fmod (-6) = -2` keeps the
loop below zero, and CPython agrees (harness case `gcd(4, -6) → -2`). -/
theorem gcd_fmod_step {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Int.gcd b (Int.fmod a b) = Int.gcd a b := by
  rw [Int.fmod_eq_emod_of_nonneg a hb, gcd_emod_step ha b]

end LeanModels.Python
