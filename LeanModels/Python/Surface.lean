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
  evaluation at `c + f₀` fuel (`Examples/python/tri/tri.py`, `Examples/python/gcd/gcd.py`);
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

/-! ### Thaw at the marshalling boundary

Since H1 a public call thaws its arguments (`Val → RVal`), so
captured/symbolic runs see a `ToVal`-marshalled argument through
`RVal.thaw`. The collapse lemmas below keep goals in the runtime normal
form (`RVal.int n`, `…listV (xs.map (thaw ∘ toVal))`), and the
`asIntList` bridge is restated in exactly the shape those runs produce. -/

@[simp] theorem thaw_toVal_int (n : Int) :
    RVal.thaw (ToVal.toVal n) = .int n := rfl
@[simp] theorem thaw_toVal_nat (n : Nat) :
    RVal.thaw (ToVal.toVal n) = .int n := rfl
@[simp] theorem thaw_toVal_bool (b : Bool) :
    RVal.thaw (ToVal.toVal b) = .bool b := rfl
@[simp] theorem thaw_toVal_str (s : String) :
    RVal.thaw (ToVal.toVal s) = .str s := rfl

/-- Thawing a marshalled list is the marshalled list of thaws (the
`List.map`-normal form; `thawList` folded away). -/
@[simp] theorem thaw_toVal_list {α} [ToVal α] (xs : List α) :
    RVal.thaw (ToVal.toVal xs)
      = .listV ((xs.map fun x => RVal.thaw (ToVal.toVal x)).toArray) := by
  simp [RVal.thaw, RVal.thawList_eq_map]

/-- `asIntList_map_int` (Logic.lean) restated at the marshalling boundary:
captured/symbolic runs see a `ToVal`-marshalled int-list argument as
`List.map (fun x => RVal.thaw (ToVal.toVal x)) xs` (simp does not rewrite
under the *unapplied* composite), so `sorted(data)` needs the bridge in
exactly this form. Wired into `py_vcgen`'s `interpLemmas`; manual
`py_simp` proofs pass it explicitly. -/
theorem asIntList_map_toVal (l : List Int) :
    asIntList (l.map fun x => RVal.thaw (ToVal.toVal x)) = some l := by
  have hfn : (fun x : Int => RVal.thaw (ToVal.toVal x)) = RVal.int := by
    funext x; rfl
  rw [hfn]
  exact asIntList_map_int l

/-- `asIntList_map_toVal` in the `Function.comp` normal form `List.map_map`
leaves behind (captured runs meet the marshalled thaw as
`RVal.thaw ∘ ToVal.toVal`). -/
theorem asIntList_map_thaw_comp (l : List Int) :
    asIntList (l.map (RVal.thaw ∘ ToVal.toVal)) = some l := by
  have hfn : (RVal.thaw ∘ (ToVal.toVal : Int → Val)) = RVal.int := by
    funext x; rfl
  rw [hfn]
  exact asIntList_map_int l

/-- Python `int` 3-tuples — the `extended_gcd` return shape (added for
`Examples/python/rsa_inverse`, the real-world demo). Deliberately monomorphic: Lean's
`×` is right-nested, so a generic `Prod` instance could not distinguish the
Python values `(a, b, c)` and `(a, (b, c))` — they inhabit the *same* Lean
type — and would silently marshal one as the other. This instance commits the
concrete `PyInt × PyInt × PyInt` type to the flat 3-tuple reading (the only
one the gallery uses); nested-tuple values stay explicit `Val`s. -/
instance : ToVal (PyInt × PyInt × PyInt) :=
  ⟨fun t => .tuple #[.int t.1, .int t.2.1, .int t.2.2]⟩

@[simp] theorem toVal_int_triple (t : PyInt × PyInt × PyInt) :
    (ToVal.toVal t : Val) = .tuple #[.int t.1, .int t.2.1, .int t.2.2] := rfl

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
whatever fuel the symbolic execution produced (`Examples/python/tri/tri.py`) —
no exact-offset fuel bookkeeping. Caveat: when the loop lemma was applied at
metavariable spans (module- and span-agnostic lemmas instantiated with `_`),
`simp` cannot index `h`; splice it with the conditional `rw [h]` instead and
discharge the `f₀ ≤ F` side goal by `omega` (see `tri_total`). -/
theorem execWhile_at_least {m : Module} {st : FrameState} {test : Expr}
    {body orelse : List Stmt} {st' : FrameState} {flow : RFlow}
    (h : ∃ fuel, execWhile m fuel st test body orelse = .ok st' flow) :
    ∃ f₀, ∀ F, f₀ ≤ F → execWhile m F st test body orelse = .ok st' flow := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, fun F hF => execWhile_mono hf (by simp) F hF⟩

/-! ## The stateful call judgment (`CallsIn`) and the frame theorem

`CallsIn` is the heap-aware call fact of docs/memory-model.md §CallsIn: a
nested call transforms a KNOWN before-world into a KNOWN after-world. A
fresh-world `CallsTo` fact is NOT a valid nested-call spec once heaps are
shared; the splice rules below consume `CallsIn`, and pure (heap-free)
callee specs lift into it via the explicit frame theorem
`CallsTo.callsIn_frame` — the `worldInv`-powered bridge that keeps every
existing pinned-state proof working. -/

/-- The stateful call judgment: some fuel runs the nested call from
`before` to `after`, returning `result` (docs/memory-model.md §CallsIn). -/
def CallsIn (m : Module) (before : World) (fname : String)
    (args : Array RVal) (after : World) (result : RVal) : Prop :=
  ∃ fuel, callIn m fuel before fname args = .ok after result

/-- Fuel-threshold form of a `CallsIn` fact (via `callIn_mono`). -/
theorem CallsIn.at_least {m : Module} {before after : World} {fname : String}
    {args : Array RVal} {result : RVal}
    (h : CallsIn m before fname args after result) :
    ∃ f₀, ∀ F, f₀ ≤ F → callIn m F before fname args = .ok after result := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, fun F hF => callIn_mono hf (by simp) F hF⟩

/-- `CallsIn` is functional (after-world and result together), across all
fuels — `fuelMono` at the `callIn` conjunct. -/
theorem CallsIn.functional {m : Module} {before : World} {fname : String}
    {args : Array RVal} {w₁ w₂ : World} {v₁ v₂ : RVal}
    (h₁ : CallsIn m before fname args w₁ v₁)
    (h₂ : CallsIn m before fname args w₂ v₂) : w₁ = w₂ ∧ v₁ = v₂ := by
  obtain ⟨f₁, hf₁⟩ := h₁
  obtain ⟨f₂, hf₂⟩ := h₂
  rcases Nat.le_total f₁ f₂ with hle | hle
  · have := (callIn_mono hf₁ (by simp) f₂ hle).symm.trans hf₂
    exact ⟨(Run.ok.inj this).1, (Run.ok.inj this).2⟩
  · have := (callIn_mono hf₂ (by simp) f₁ hle).symm.trans hf₁
    exact ⟨(Run.ok.inj this).1.symm, (Run.ok.inj this).2.symm⟩

/-- **The frame theorem**: in a heap-free module a pure `CallsTo` spec
lifts to a `CallsIn` fact at the public geometry — the callee cannot touch
the heap, so it hands the fresh world back unchanged (`worldInv` through
`callIn_world`) and returns the thaw of the public value
(`RVal.eq_thaw_of_freeze` inverts the boundary freeze). The heap-freedom
hypothesis is an autoparam (`rfl` computes on concrete modules). Scope
note: the world is pinned at `initWorld m` because a heap-free body may
still READ the heap through ref-carrying arguments — a ∀-world frame needs
ref-free arguments too, and no current consumer wants it. -/
theorem CallsTo.callsIn_frame {m : Module} {fname : String}
    {args : Array Val} {v : Val} (h : CallsTo m fname args v)
    (hm : m.heapFree = true := by first | rfl | decide)
    (hv : Val.listFree v = true := by first | rfl | decide) :
    CallsIn m (initWorld m) fname (RVal.thawArgs args)
      (initWorld m) (RVal.thaw v) := by
  obtain ⟨fuel, hf⟩ := h
  unfold callFunction at hf
  revert hf
  cases hc : callIn m fuel (initWorld m) fname (RVal.thawArgs args) with
  | ok w' rv =>
    intro hf
    rw [Run.toPublic_ok] at hf
    have hrv : rv = RVal.thaw v :=
      RVal.eq_thaw_of_freezeB w'.heap fuel rv hf hv
    subst hrv
    obtain rfl := callIn_world hm hc
    exact ⟨fuel, hc⟩
  | exn w' e => intro hf; cases hf
  | timeout => intro hf; cases hf
  | unsupported msg => intro hf; cases hf

/-- The `callIn` threshold form of a public `CallsTo` fact — the splice a
recursion proof (or a callee-spec rule) rewrites a nested call site with.
Pinned geometry (docs/memory-model.md): in a HEAP-FREE module (autoparam;
`rfl` computes it on concrete modules) a nested `callIn` site inside a
public run sits at exactly the public fresh world (`initWorld m` —
`worldInv`), with thawed arguments; the callee returns the thaw of the
spec's value (`RVal.eq_thaw_of_freeze`) and hands the world back
unchanged, so the rewrite is fully determined. The composition
`CallsTo.callsIn_frame` ∘ `CallsIn.at_least`. -/
theorem CallsTo.callIn_at_least {m : Module} {fname : String}
    {args : Array Val} {v : Val} (h : CallsTo m fname args v)
    (hm : m.heapFree = true := by first | rfl | decide)
    (hv : Val.listFree v = true := by first | rfl | decide) :
    ∃ f₀, ∀ F, f₀ ≤ F →
      callIn m F (initWorld m) fname (RVal.thawArgs args)
        = .ok (initWorld m) (RVal.thaw v) :=
  (h.callsIn_frame hm hv).at_least

/-! ## The generic while rule -/

/-- **The generic total-correctness while rule.** Instantiate with a logical
state `σ`, its rendering `toEnv` into interpreter environments, an invariant,
a boolean continuation condition (the truthiness of the loop test), the body's
logical effect `step`, and a decreasing measure. The conclusion: from any
invariant state, *some* fuel runs the loop to completion, landing in an
invariant state where the test is false. All fuel bookkeeping is internal —
a loop lemma becomes pure invariant/measure mathematics plus two symbolic
executions (`Examples/python/tri/tri.py`, `Examples/python/gcd/gcd.py`).

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
goals, and symbolic execution cannot run on an unknown AST.

Pinned-world geometry (H1 stage 1): the rule runs the loop at ONE world
`w`, pinned through test, body, and exit — the shape the walker needs (a
known mid-state), justified by stage-1 world invariance (`worldInv`); the
`htv` obligation is the `Res`-valued truthiness decision (a `.ref` test
value would be loud, so the obligation also proves decidedness). -/
theorem execWhile_total_of_invariant {σ : Type}
    (m : Module) (test : Expr) (body : List Stmt) (w : World)
    (toEnv : σ → Env) (Inv : σ → Prop) (Cont : σ → Bool)
    (step : σ → σ) (μ : σ → Nat) (tv : σ → RVal)
    (htest : ∀ s, Inv s →
      ∃ f₀, ∀ F, f₀ ≤ F →
        evalExpr m F ⟨w, toEnv s⟩ test = .ok ⟨w, toEnv s⟩ (tv s))
    (htv : ∀ s, Inv s → truthy (tv s) = .ok (Cont s))
    (hbody : ∀ s, Inv s → Cont s = true →
      ∃ f₀, ∀ F, f₀ ≤ F →
        execStmts m F ⟨w, toEnv s⟩ body = .ok ⟨w, toEnv (step s)⟩ .next)
    (hinv : ∀ s, Inv s → Cont s = true → Inv (step s))
    (hdec : ∀ s, Inv s → Cont s = true → μ (step s) < μ s) :
    ∀ s, Inv s →
      ∃ s', Inv s' ∧ Cont s' = false ∧
        ∃ F, execWhile m F ⟨w, toEnv s⟩ test body []
              = .ok ⟨w, toEnv s'⟩ .next := by
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
      simp only [Run.ok_bind]
      rw [truthyH_of_truthy (htv s hs)]
      simp only [Run.liftRes_ok, Run.ok_bind]
      rw [hc]
      simp only [if_true]
      rw [hfb (ft + fb + F) (by omega)]
      simp only [Run.ok_bind]
      exact hF' (ft + fb + F) (by omega)
    · -- test is false: exit immediately (orelse = [] finishes in one step)
      have hcf : Cont s = false := by revert hc; cases Cont s <;> simp
      refine ⟨s, hs, hcf, ft + 2, ?_⟩
      rw [execWhile]
      rw [hft (ft + 1) (by omega)]
      simp only [Run.ok_bind]
      rw [truthyH_of_truthy (htv s hs)]
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
`ZeroDivisionError` guard (`Examples/python/gcd/gcd.py`). -/
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

open Lean Elab Tactic in
/-- `py_check` — the tactic twin of `#py_check`: close a concrete-run *goal*
by making Lean actually run the program. It handles exactly the two concrete
judgment shapes — `f(args) ==> v` (supplies the fuel witness, then kernel
evaluation decides `callFunction … = .ok (toVal v)` by `rfl`) and
`f(args) ==>! e` (same, against `.exn e`) — at the command's fixed generous
fuel (4096; concrete runs cost time proportional to actual steps, not to
fuel, so generosity is free).

The honest boundary: the closing step is *kernel reduction*, and kernel
reduction happily runs branch-free bodies on open terms too — `add(a, b)
==> a + b` with free `a`, `b` reduces to `.ok (.int (a + b)) = .ok (.int
(a + b))` without ever inspecting the variables, so bare `rfl` would close
a genuinely symbolic theorem. That would let the non-vacuity checker double
as the proof, so `py_check` refuses up front: the guard below fails on any
goal whose arguments or result mention a variable (free or metavariable),
BEFORE attempting the run. Concrete non-vacuity is this tactic's single
job; symbolic goals — `add(a, b) ==> a + b`, `my_abs(x) ==> |x|`, any
`~~>`/`⇓` form, a loop bound to induct on — belong to `py_prove` and the
loop machinery.

Failure shape: on a concrete goal whose run decides *differently* from what
the goal claims (wrong value, wrong exception, or a 4096-fuel timeout), the
error STATES THE COMPUTED VALUE — "the run (fuel 4096) produced `.ok (.int
10)` / but the goal claims `.ok (.int 15)`" — by evaluating the run once
more on the failure path; the symbolic-goal guard above keeps its own
message. Implementation note (first-combinator commit-safety): the run
attempt is all-tactic with an explicit state save/restore — an `exact
⟨4096, by rfl⟩` alternative would *commit* inside a combinator even when
the nested `by` block fails (see the `py_prove` docstring), and a
`first | … | fail` shape could not compute the diagnostic, so the failure
path is taken by hand. -/
elab (name := pyCheckTactic) "py_check" : tactic => do
  let msg := "py_check: not a concrete run — the goal must be `f(args) ==> v` or `f(args) ==>! e` with literal arguments, and the run at fuel 4096 must produce exactly the stated value (resp. exception); symbolic goals want `py_prove` or a loop lemma instead"
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
  unless t.isAppOfArity ``CallsTo 4 || t.isAppOfArity ``Raises 4 do
    throwError msg
  -- The symbolic-goal guard: arguments and result must be variable-free
  -- (kernel reduction would otherwise "prove" symbolic branch-free goals).
  -- Its message stays the curated pointer above — a symbolic goal has no
  -- "computed value" to report.
  let symbolic (e : Lean.Expr) : Bool := e.hasFVar || e.hasExprMVar
  if symbolic (t.getArg! 2) || symbolic (t.getArg! 3) then
    throwError msg
  let s ← saveState
  try
    evalTactic (← `(tactic| (refine ⟨4096, ?_⟩
                             rfl)))
    return
  catch _ =>
    s.restore
  -- Concrete goal, run decided differently: evaluate the run once more and
  -- say what it actually produced vs what the goal claims.
  let runE := Lean.mkApp4 (Lean.mkConst ``callFunction) (t.getArg! 0)
    (t.getArg! 1) (t.getArg! 2) (Lean.mkNatLit 4096)
  let claimedE :=
    if t.isAppOfArity ``CallsTo 4 then
      Lean.mkApp2 (Lean.mkConst ``Res.ok) (Lean.mkConst ``Val) (t.getArg! 3)
    else
      Lean.mkApp2 (Lean.mkConst ``Res.exn) (Lean.mkConst ``Val) (t.getArg! 3)
  -- `Meta.reduce` computes the value; the default-simp pass afterwards is
  -- display-only (it renders `Int.ofNat 10` back as the literal `10`).
  let present (e : Lean.Expr) : TacticM Lean.Expr := do
    let e ← Meta.reduce e (explicitOnly := false)
    try
      let ctx ← Meta.Simp.mkContext {} #[← Meta.getSimpTheorems]
        (← Meta.getSimpCongrTheorems)
      let (r, _) ← Meta.simp e ctx
      pure r.expr
    catch _ => pure e
  let produced? ← try some <$> present runE catch _ => pure none
  let claimed ← try present claimedE catch _ => pure claimedE
  match produced? with
  | some produced =>
    throwError "py_check: the run (fuel 4096) produced{indentExpr produced}\nbut the goal claims{indentExpr claimed}"
  | none => throwError msg

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
a recursive run into a symbolic execution (`Examples/python/fib/fib.py`): `e` is
any `CallsTo` fact (typically the induction hypothesis at a smaller
argument); the macro takes its `callIn` fuel-threshold form
(`CallsTo.callIn_at_least` — since H1 the nested call sites inside a
public run are `callIn` at the pinned public world, so that is the splice
shape) and symbolically normalizes it, binding the threshold `f₀` and
`h : ∀ F, f₀ ≤ F → callIn ⟨…⟩ F (initWorld _) … = .ok (initWorld _) v`
with the program literal `prog` unfolded. `h` is a *conditional rewrite
rule*: after executing the enclosing body (`unfold callFunction;
rw [callIn.eq_2]; py_simp […]`), close the frozen recursive call sites
with `simp (disch := omega) only [h]` — `omega` discharges the `f₀ ≤ F`
side conditions at whatever fuel the execution produced, so no
exact-offset fuel bookkeeping ever appears (pick any generous slack for
the outer witness). Implementation note: the unfold and the normalization
are one fused `py_simp [prog] at h` — the two-step `simp only [prog] at h;
py_simp at h` form fails with "no progress" on hypotheses that need no
cast normalization. -/
macro "py_lift" "⟨" fid:ident "," hid:ident "⟩" " := " e:term " with "
    "[" args:(simpStar <|> simpErase <|> simpLemma),* "]" : tactic => do
  let extra : Syntax.TSepArray
      [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
       `Lean.Parser.Tactic.simpLemma] "," := ⟨args.elemsAndSeps⟩
  `(tactic|
    (obtain ⟨$fid, $hid⟩ := ($e).callIn_at_least
     py_simp [$extra,*] at $hid:ident))

open Lean Elab Tactic in
/-- Post-check appended to every `py_prove` pipeline (internal — not meant
to be called directly): when the pipeline's residual goals still mention
interpreter internals (`callFunction`/`execWhile`/`execStmts`/`Res`/`Val`/
`Flow`, …), the run left interpreter *state* unresolved — a raw goal dump
would be noise, so fail with a curated message pointing at the loop and
manual routes instead. Residual goals that are clean arithmetic pass
through untouched (they are useful; `py_prove` leaves them on purpose). -/
elab "py_prove_residual_guard" : tactic => do
  let roots : List Name :=
    [``callFunction, ``callIn, ``execWhile, ``execFor, ``execStmts,
     ``execStmt, ``evalExpr, ``evalExprs, ``Res, ``Run, ``Val, ``RVal,
     ``RFlow, ``FrameState, ``World]
  for g in (← getGoals) do
    let t ← instantiateMVars (← g.getType)
    let dirty := t.find? fun e =>
      match e with
      | .const n _ => roots.any fun r => r == n || r.isPrefixOf n
      | _ => false
    if dirty.isSome then
      throwError "py_prove's recipe covers straight-line and simple branching bodies; this body left interpreter state unresolved. For a loop, use `py_vcgen [prog] (inv := fun … => …) (dec := fun … => …)` — or bare `py_vcgen [prog]` to have the invariant and measure requested as goals; for the manual route see `py_simp`/`py_threshold`/`execWhile_at_least`."

open Lean Lean.Parser.Tactic in
/-- `py_prove [prog, extra…]` closes total-correctness goals (`f(a, b) ==> v`,
`f(a) ==>! e`) for straight-line *and branching* loop-free bodies: it
supplies a fuel witness (32 — ample for loop-free bodies), symbolically
executes the interpreter with `py_simp` (pass the loaded program literal,
e.g. `py_prove [add]`), and discharges residual value equations with
`rfl`/`omega`. The bracket list is a `py_simp` lemma list, so besides
program literals it accepts local *hypotheses* the symbolic run needs as
rewrite facts — the standard use is a divisor guard: on
`theorem mod_pos (a b : PyInt) (hb : b ≠ 0) : arith.mod(a, b) ==> …`,
`py_prove [arith, hb]` lets `hb` decide `%`'s `ZeroDivisionError` branch,
which bare `py_prove [arith]` leaves stuck (same for `//`, and for any
branch guard a precondition settles). A symbolic branch (`if x < 0:`) survives execution as an
`ite` inside the existential nest; the branch-splitting attempt case-splits
it with `split` (which reaches under the `∃` binders — `split_ifs` does not
exist on this toolchain), re-executes each arm with `py_simp`, and finishes
with `omega`, so `Examples/python/my_abs/my_abs.py`'s `my_abs(x) ==> |x|` closes by
bare `py_prove [my_abs]`. Every attempt is all-tactic and (where it must
close the goal) `done`-guarded — an `exact … (by …)` alternative would
*commit* inside `first` even when its nested `by` block fails (the failure
is recovered with `sorry` and merely logged as a raw goal dump), making
every fallback after it unreachable and the "proof" silently sorried;
that exact trap produced the interpreter-state walls the residual guard
below now curates. Loops and recursion still need their
invariant/induction lemmas (see `py_lift` / `execWhile_at_least`) — that
automation arrives with the bridge layer; `py_prove` is the front door that
grows, not a promise it keeps yet. Failure shape: when the pipeline leaves
goals that still mention interpreter internals (a loop's frozen
`execWhile`, `Res`/`Val` state), `py_prove` fails with a curated pointer to
`py_vcgen`/`py_simp`/`py_threshold` instead of surfacing the raw dump
(`py_prove_residual_guard` above); clean *arithmetic* residuals are still
left open — those are useful. -/
macro "py_prove" "[" args:(simpStar <|> simpErase <|> simpLemma),* "]" : tactic => do
  let extra : Syntax.TSepArray
      [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
       `Lean.Parser.Tactic.simpLemma] "," := ⟨args.elemsAndSeps⟩
  `(tactic|
    (intros
     first
       | (refine ⟨32, ?_⟩
          py_simp [callFunction, callIn, $extra,*]
          first
            | done
            | split <;> py_simp <;> omega
            | omega
          done)
       | (refine CallsTo.intro 32 ?_
          py_simp [callFunction, callIn, $extra,*]
          done)
       | refine ⟨32, ?_⟩ <;> py_simp [callFunction, callIn, $extra,*]
       | (py_simp [callFunction, callIn, $extra,*]
          all_goals try (first | rfl | omega))
     py_prove_residual_guard))

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

/-- Determinism on the int-triple surface — `CallsTo.typed_int_eq`'s 3-tuple
analog (added for `Examples/python/rsa_inverse`, whose `extended_gcd` returns a
Python 3-tuple): a `⇓`-bound triple result equals the triple value of any
`CallsTo` fact; componentwise injectivity peels the marshalling. -/
theorem CallsTo.typed_int3_eq {m : Module} {f : String} {args : Array Val}
    {r e : PyInt × PyInt × PyInt} (h : CallsTo m f args (ToVal.toVal r))
    (ht : CallsTo m f args (ToVal.toVal e)) : r = e := by
  have := CallsTo.functional h ht
  obtain ⟨r1, r2, r3⟩ := r
  obtain ⟨e1, e2, e3⟩ := e
  simp_all

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

Per-example directories `Examples/python/<name>/` split an example into
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
(e.g. `Examples.python.tri.spec`), rewrites the module's last component `spec` →
`proof`, resolves `<proof-module-namespace>.<decl-name>`
(`Examples.python.tri.proof.tri_total`), and closes the goal with
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
`Examples/python/gcd/gcd.py`'s `gcd_total`. The sign hypotheses
are not decoration: `Int.gcd 4 (-6) = 2` but `(4).fmod (-6) = -2` keeps the
loop below zero, and CPython agrees (harness case `gcd(4, -6) → -2`). -/
theorem gcd_fmod_step {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Int.gcd b (Int.fmod a b) = Int.gcd a b := by
  rw [Int.fmod_eq_emod_of_nonneg a hb, gcd_emod_step ha b]

end LeanModels.Python
