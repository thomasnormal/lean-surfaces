import LeanModels.Python.VC
import LeanModels.Python.Surface

/-!
# Control-flow and interprocedural rules (`py_vcgen` layer 2)

Layer 1 (VC.lean) built the flow-aware triples (`PyPost`/`PyStmtTriple`/
`PyTriple`) over frame states; this file adds the rules that *consume* the
`brk`/`cont`/`ret` arms layer 1 plumbed, plus the bridges that connect
triples to the arrow surface (Surface.lean).

* **`PyStmtTriple.whileLoop`** — THE loop rule in the triple vocabulary:
  invariant `Inv : FrameState → Prop` (directly on frame states — no
  `σ`/`toEnv` rendering layer), measure `μ : FrameState → Nat`, test-value
  function `tv : FrameState → RVal`. Truthiness is `Res`-valued since H1,
  so the rule carries a DECIDEDNESS hypothesis (`htv`: the test value's
  truthiness decides — a loud `.ref` test would refuse it) alongside the
  exit implication; the body triple's arms route Python's loop flow exactly
  as before (`next`/`cont` re-establish the invariant with a smaller
  measure, `brk` lands in the loop's `Q.next`, `ret` propagates to `Q.ret`,
  `err` — state-aware — to `Q.err`). Restriction: `orelse = #[]` only.
  The engine is `execWhile_of_invariant` (strong induction on the measure);
  the old `execWhile_total_of_invariant` (Surface.lean) remains the
  `py_loop` backend — this rule is what `py_vcgen` targets.

* **Interprocedural rules** — `EvalsToList` (pinned-state like `EvalsTo`),
  `EvalsTo.call` (the compositional primitive: a call *expression*
  evaluates to the THAW of the callee's public result, given a `CallsTo`
  fact — any `CallsTo` fact: a `@[py_spec]` lemma or a local hypothesis,
  e.g. a recursion IH), and `PyStmtTriple.call`/`PyTriple.call`. Stage-1
  geometry: a nested call site inside a public run sits at exactly the
  public fresh world (`st.world = initWorld m`, by `worldInv`), its
  arguments are thawed boundary values, and the callee hands the world
  back unchanged (`CallsTo.callIn_at_least`, Surface.lean) — so the splice
  is fully determined. The `hworld` hypothesis is the pinned-geometry
  obligation; the walker discharges it by `rfl` at its literal states.
  This rule set is replaced by the stateful `CallsIn` machinery when the
  dict tier lands (docs/memory-model.md §CallsIn).

* **The `@[py_spec]` registry** — unchanged: `@[py_spec]` marks a lemma
  whose conclusion is `CallsTo`-shaped (surface arrow form). Retrieval is
  `Lean.labelled `py_spec` (CoreM); the rules take the instantiated
  `CallsTo` fact as an ordinary hypothesis, so registered and local specs
  are consumed identically.

* **Bridge theorems** — `callsTo_iff_triple` and friends, re-shaped for
  the wrapper decomposition: the whole-body triple runs from the entry
  state `⟨initWorld m, mkCallEnv f.params (args.map RVal.thaw)⟩` (the
  public call thaws its arguments), and its `ret` arm pins the returned
  runtime value to `RVal.thaw v` — the roundtrip lemmas
  (`RVal.freeze_thaw`/`RVal.eq_thaw_of_freeze`) carry the value through
  the wrapper's deep-freeze in both directions. The raise-side pair
  (`PyTriple.raises`/`Raises.toTriple`/`raises_iff_triple`) goes through
  the state-aware `err` arm (the raise state is erased at the public
  boundary — `Res.exn` carries no state — so the arm's spec there is
  state-agnostic: `fun e' _ => e' = e`).

Recursion pattern (proved in VCTests.lean): induct on the *math* variable;
in the step case the IH is a local `CallsTo` fact at the smaller argument,
consumed by `PyStmtTriple.call`/`EvalsTo.call` exactly as a registered
spec would be; close the case through `PyTriple.callsTo`. No fixpoint rule
is needed — `CallsTo`'s `∃ fuel` does the tying, `fuelMono` the splicing.
-/

namespace LeanModels.Python

/-- Destructure a nonzero-threshold bound: `F ≥ t + 1` is a successor
`F' + 1` with `F' ≥ t` (private twin of VC.lean's helper). -/
private theorem succ_le_dest {t F : Nat} (h : t + 1 ≤ F) :
    ∃ F', F = F' + 1 ∧ t ≤ F' := ⟨F - 1, by omega, by omega⟩

/-! ## Argument lists: `EvalsToList` -/

/-- Terminating PURE evaluation of an expression list (the `evalExprs`
analog of `EvalsTo`: state returned unchanged, same `∃ fuel` shape, same
`at_least` accessor) — the argument-vector interface of the call rules.
Build it from per-argument `EvalsTo` facts with `nil`/`cons`, or from one
concrete run (`of_eval`). -/
def EvalsToList (m : Module) (st : FrameState) (es : List Expr)
    (vs : List RVal) : Prop :=
  ∃ fuel, evalExprs m fuel st es = .ok st vs

namespace EvalsToList

/-- Introduce `EvalsToList` from one concrete run (any fuel). -/
theorem of_eval {m : Module} {fuel : Nat} {st : FrameState} {es : List Expr}
    {vs : List RVal} (h : evalExprs m fuel st es = .ok st vs) :
    EvalsToList m st es vs := ⟨fuel, h⟩

/-- Fuel-threshold form (the `EvalsTo.at_least` analog, via `evalExprs_mono`). -/
theorem at_least {m : Module} {st : FrameState} {es : List Expr}
    {vs : List RVal} (h : EvalsToList m st es vs) :
    ∃ t, ∀ F ≥ t, evalExprs m F st es = .ok st vs := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, fun F hF => evalExprs_mono hf (by simp) F hF⟩

/-- The empty argument list. -/
theorem nil {m : Module} {st : FrameState} : EvalsToList m st [] [] := ⟨1, rfl⟩

/-- Prepend one evaluated argument (thresholds spliced at a summed bound). -/
theorem cons {m : Module} {st : FrameState} {e : Expr} {v : RVal}
    {es : List Expr} {vs : List RVal} (hv : EvalsTo m st e v)
    (hvs : EvalsToList m st es vs) :
    EvalsToList m st (e :: es) (v :: vs) := by
  obtain ⟨t1, h1⟩ := hv.at_least
  obtain ⟨t2, h2⟩ := hvs.at_least
  refine ⟨t1 + t2 + 1, ?_⟩
  simp [evalExprs, h1 (t1 + t2) (by omega), h2 (t1 + t2) (by omega)]

end EvalsToList

/-! ## The while rule -/

/-- The while rule's engine, at the `execWhile` level: from any invariant
state some fuel threshold lands the whole loop in the arm `Q` prescribes.
Strong induction on the measure, with the body's `brk`/`ret`/`err` escapes
routed to `Q`'s arms instead of being ruled out. `orelse = []` only
(module docstring). Instantiate directly (instead of via
`PyStmtTriple.whileLoop`) when the loop occurrence is already an
`execWhile` term, e.g. after hand-unrolling an iteration à la
`Examples/python/rsa_inverse`. -/
theorem execWhile_of_invariant {m : Module} {test : Expr} {body : List Stmt}
    {Q : PyPost} (Inv : FrameState → Prop) (μ : FrameState → Nat)
    (tv : FrameState → RVal)
    (htest : ∀ st, Inv st → EvalsTo m st test (tv st))
    (htv : ∀ st, Inv st → ∃ b, truthy (tv st) = .ok b)
    (hexit : ∀ st, Inv st → truthy (tv st) = .ok false → Q.next st)
    (hbody : ∀ n, PyTriple m
        (fun st => Inv st ∧ truthy (tv st) = .ok true ∧ μ st = n) body
        { next := fun st' => Inv st' ∧ μ st' < n
          ret := Q.ret
          brk := Q.next
          cont := fun st' => Inv st' ∧ μ st' < n
          err := Q.err }) :
    ∀ st, Inv st → ∃ t, ∀ F ≥ t, Q.holds (execWhile m F st test body []) := by
  intro st hI
  generalize hn : μ st = n
  induction n using Nat.strongRecOn generalizing st with
  | ind n ih =>
    obtain ⟨tt, ht⟩ := (htest st hI).at_least
    obtain ⟨b, hb⟩ := htv st hI
    cases b
    · -- test false: exit through the (empty) orelse into `Q.next`
      refine ⟨tt + 2, fun F hF => ?_⟩
      obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
      obtain ⟨F'', rfl, hF''⟩ := succ_le_dest hF'
      simpa [execWhile, ht (F'' + 1) (by omega), truthyH_of_truthy hb, execStmts]
        using hexit st hI hb
    · -- test true: run the body, dispatch on how it landed
      obtain ⟨r, tb, hr, hrun⟩ := (hbody n).exec ⟨hI, hb, hn⟩
      cases r with
      | ok st' flow =>
        cases flow with
        | next =>
          obtain ⟨hI', hlt⟩ := hr
          obtain ⟨tw, hw⟩ := ih (μ st') hlt st' hI' rfl
          have h0 := hw tw (Nat.le_refl tw)
          have hpin := execWhile_mono rfl (PyPost.holds_ne_timeout h0)
          refine ⟨tt + tb + tw + 1, fun F hF => ?_⟩
          obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
          rw [execWhile, ht F' (by omega)]
          simp only [Run.ok_bind, truthyH_of_truthy hb, Run.liftRes_ok, if_true]
          rw [hrun F' (by omega)]
          simp only [Run.ok_bind]
          rw [hpin F' (by omega)]
          exact h0
        | cont =>
          -- `continue` re-tests: an iteration like `next` (same measure step)
          obtain ⟨hI', hlt⟩ := hr
          obtain ⟨tw, hw⟩ := ih (μ st') hlt st' hI' rfl
          have h0 := hw tw (Nat.le_refl tw)
          have hpin := execWhile_mono rfl (PyPost.holds_ne_timeout h0)
          refine ⟨tt + tb + tw + 1, fun F hF => ?_⟩
          obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
          rw [execWhile, ht F' (by omega)]
          simp only [Run.ok_bind, truthyH_of_truthy hb, Run.liftRes_ok, if_true]
          rw [hrun F' (by omega)]
          simp only [Run.ok_bind]
          rw [hpin F' (by omega)]
          exact h0
        | brk =>
          -- `break` skips orelse: unified into the loop's `next` exit
          refine ⟨tt + tb + 1, fun F hF => ?_⟩
          obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
          rw [execWhile, ht F' (by omega)]
          simp only [Run.ok_bind, truthyH_of_truthy hb, Run.liftRes_ok, if_true]
          rw [hrun F' (by omega)]
          simpa using hr
        | ret v =>
          -- `return` escapes the loop into the outer `ret` arm
          refine ⟨tt + tb + 1, fun F hF => ?_⟩
          obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
          rw [execWhile, ht F' (by omega)]
          simp only [Run.ok_bind, truthyH_of_truthy hb, Run.liftRes_ok, if_true]
          rw [hrun F' (by omega)]
          simpa using hr
      | exn st' e =>
        refine ⟨tt + tb + 1, fun F hF => ?_⟩
        obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
        rw [execWhile, ht F' (by omega)]
        simp only [Run.ok_bind, truthyH_of_truthy hb, Run.liftRes_ok, if_true]
        rw [hrun F' (by omega)]
        simpa using hr
      | timeout => exact (PyPost.holds_ne_timeout hr rfl).elim
      | unsupported msg => exact hr.elim

/-- **The while rule** in the triple vocabulary (module docstring): from
invariant `Inv` with measure `μ`, test-value function `tv`, and the
truthiness decision `htv`, a body triple whose arms route Python's loop
flow yields the loop statement's triple from precondition `Inv`
(strengthen with `PyStmtTriple.consequence`). Restriction: `orelse = #[]`
(orelse-carrying specs deferred). The old rule stays; `py_loop` still
targets it. -/
theorem PyStmtTriple.whileLoop {m : Module} {test : Expr} {body : Array Stmt}
    {sp : Span} {Q : PyPost} (Inv : FrameState → Prop) (μ : FrameState → Nat)
    (tv : FrameState → RVal)
    (htest : ∀ st, Inv st → EvalsTo m st test (tv st))
    (htv : ∀ st, Inv st → ∃ b, truthy (tv st) = .ok b)
    (hexit : ∀ st, Inv st → truthy (tv st) = .ok false → Q.next st)
    (hbody : ∀ n, PyTriple m
        (fun st => Inv st ∧ truthy (tv st) = .ok true ∧ μ st = n) body.toList
        { next := fun st' => Inv st' ∧ μ st' < n
          ret := Q.ret
          brk := Q.next
          cont := fun st' => Inv st' ∧ μ st' < n
          err := Q.err }) :
    PyStmtTriple m Inv (.whileLoop test body #[] sp) Q := by
  intro st hI
  obtain ⟨t, ht⟩ := execWhile_of_invariant Inv μ tv htest htv hexit hbody st hI
  refine ⟨t + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  simpa [execStmt] using ht F' hF'

/-- List-level singleton form of the while rule (a loop standing alone as a
statement list — e.g. a whole function body); for a loop in mid-list
position feed `PyStmtTriple.whileLoop` to `PyTriple.seq` instead. -/
theorem PyTriple.whileLoop {m : Module} {test : Expr} {body : Array Stmt}
    {sp : Span} {Q : PyPost} (Inv : FrameState → Prop) (μ : FrameState → Nat)
    (tv : FrameState → RVal)
    (htest : ∀ st, Inv st → EvalsTo m st test (tv st))
    (htv : ∀ st, Inv st → ∃ b, truthy (tv st) = .ok b)
    (hexit : ∀ st, Inv st → truthy (tv st) = .ok false → Q.next st)
    (hbody : ∀ n, PyTriple m
        (fun st => Inv st ∧ truthy (tv st) = .ok true ∧ μ st = n) body.toList
        { next := fun st' => Inv st' ∧ μ st' < n
          ret := Q.ret
          brk := Q.next
          cont := fun st' => Inv st' ∧ μ st' < n
          err := Q.err }) :
    PyTriple m Inv [.whileLoop test body #[] sp] Q :=
  PyTriple.single (PyStmtTriple.whileLoop Inv μ tv htest htv hexit hbody)

/-! ## Interprocedural rules -/

/-- A call *expression* evaluates to the thaw of the callee's public
result: the compositional primitive behind `PyStmtTriple.call`, and the
splice point for calls in any other expression position (`return f(x)`,
operands). Hypotheses: the callee name is not shadowed by a local binding,
the arguments evaluate to the THAWED spec arguments (`EvalsToList` — at a
literal call site this is the captured evaluation itself), the frame sits
at the public fresh world (`hworld` — the stage-1 pinned geometry, closed
by `rfl` at literal states), and a `CallsTo` fact — a `@[py_spec]` lemma
instantiated at the argument values, or a *local* hypothesis such as a
recursion proof's IH — gives the callee's result. The `findFunction`
lookup is *derived* from the `CallsTo` fact, not assumed. -/
theorem EvalsTo.call {m : Module} {st : FrameState} {fname : String}
    {argEs : Array Expr} {args : Array Val} {v : Val} {sp sp' : Span}
    (hlocal : Env.lookup st.locals fname = Option.none)
    (hargs : EvalsToList m st argEs.toList (RVal.thawList args.toList))
    (hworld : st.world = initWorld m)
    (hspec : CallsTo m fname args v)
    (hglob : lookupG (moduleGlobals m).1 fname = Option.none := by rfl)
    (hm : m.heapFree = true := by rfl)
    (hv : Val.listFree v = true := by rfl) :
    EvalsTo m st (.call (.name fname sp) argEs Option.none sp') (RVal.thaw v) := by
  obtain ⟨w, locals⟩ := st
  simp only at hworld hlocal hargs
  subst hworld
  obtain ⟨ta, ha⟩ := hargs.at_least
  obtain ⟨tc, hc⟩ := hspec.callIn_at_least hm hv
  have hfn : (findFunction m fname).isSome = true := by
    cases hff : findFunction m fname with
    | none =>
      have h1 := hc (tc + 1) (by omega)
      rw [callIn, hff] at h1
      cases h1
    | some f => simp
  refine ⟨ta + tc + 1, ?_⟩
  have ha' := ha (ta + tc) (by omega)
  have hc' := hc (ta + tc) (by omega)
  have hc'' : callIn m (ta + tc) (initWorld m) fname
      (RVal.thawList args.toList).toArray = Run.ok (initWorld m) (RVal.thaw v) := hc'
  simp [evalExpr, hlocal, hglob, hfn, findClass_heapFree hm fname, ha', hc'']

/-- **The call rule** — `x = f(e₁, …, eₖ)` consuming a callee spec: from
each `P`-state, the callee name unshadowed, the pinned public world, the
thawed argument values (`EvalsToList`), a `CallsTo` fact at the boundary
values (registered `@[py_spec]` lemma or local hypothesis), and `Q.next`
at the thawed result bound to `x`. Derived: `assignName` ∘ `EvalsTo.call`,
no interpreter work. -/
theorem PyStmtTriple.call {m : Module} {P : FrameState → Prop} {Q : PyPost}
    {x fname : String} {argEs : Array Expr} {spx spf spc spa : Span}
    (h : ∀ st, P st → Env.lookup st.locals fname = Option.none ∧
        st.world = initWorld m ∧
        ∃ args v, EvalsToList m st argEs.toList (RVal.thawList args.toList) ∧
          Val.listFree v = true ∧
          CallsTo m fname args v ∧
          Q.next ⟨st.world, Env.set st.locals x (RVal.thaw v)⟩)
    (hglob : lookupG (moduleGlobals m).1 fname = Option.none := by rfl)
    (hm : m.heapFree = true := by rfl) :
    PyStmtTriple m P
      (.assign #[.name x spx] (.call (.name fname spf) argEs Option.none spc) spa)
      Q :=
  PyStmtTriple.assignName fun st hP =>
    let ⟨hlocal, hworld, _args, v, hvs, hlf, hc, hQ⟩ := h st hP
    ⟨RVal.thaw v, EvalsTo.call hlocal hvs hworld hc hglob hm hlf, hQ⟩

/-- List-level form of the call rule: `x = f(…)` followed by `rest`, with
the callee's postcondition (thawed result bound to `x`) as the
midcondition `R`. -/
theorem PyTriple.call {m : Module} {P R : FrameState → Prop} {Q : PyPost}
    {x fname : String} {argEs : Array Expr} {spx spf spc spa : Span}
    {rest : List Stmt}
    (h : ∀ st, P st → Env.lookup st.locals fname = Option.none ∧
        st.world = initWorld m ∧
        ∃ args v, EvalsToList m st argEs.toList (RVal.thawList args.toList) ∧
          Val.listFree v = true ∧
          CallsTo m fname args v ∧
          R ⟨st.world, Env.set st.locals x (RVal.thaw v)⟩)
    (hrest : PyTriple m R rest Q)
    (hglob : lookupG (moduleGlobals m).1 fname = Option.none := by rfl)
    (hm : m.heapFree = true := by rfl) :
    PyTriple m P
      (.assign #[.name x spx] (.call (.name fname spf) argEs Option.none spc) spa
        :: rest) Q :=
  PyTriple.seq (PyStmtTriple.call h hglob hm) hrest

/-! ## The `@[py_spec]` registry -/

/-- Marks a callee specification for the py_vcgen layer. Required shape:
after the lemma's binders and precondition hypotheses, the conclusion is
`CallsTo`-shaped — surface arrow form, `f(a, b) ==> v` (the form spec.lean
files already export; `⇓` elaborates to the same `CallsTo`). Retrieval:
`Lean.labelled `py_spec` (CoreM). The call rules consume the resulting
`CallsTo` fact as an ordinary hypothesis, so attribute-registered and
local specs (e.g. a recursion IH) are interchangeable; to move between
this arrow form and the triple layer use `callsTo_iff_triple`. Distinct
from core's `@[spec]` (the mvcgen registry the raw ∀-fuel corollaries
use) — `@[py_spec]` is the *arrow-form* registry of this DSL's vcgen. -/
register_label_attr py_spec

/-! ## Bridges: triples ⇄ the arrow surface

Whole-function bridges — entry state
`⟨initWorld m, mkCallEnv f.params (args.map RVal.thaw)⟩` (the public call
thaws its arguments into a fresh world), `Q.ret` pinning the returned
runtime value to `RVal.thaw v` (the wrapper's deep-freeze then decides
`.ok v` — the roundtrip lemmas), the `next` arm as Python's implicit
`return None`. These keep every spec.lean statement in arrow form while
proofs go through triples. Side hypotheses (`findFunction`/`argsOk`/
`localsOk`/arity) close by `rfl`/`py_simp` at concrete modules; the
backward `CallsTo` direction *derives* the guards from the successful run
instead. -/

/-- Triple → arrow, value side, general-arity form (F1 defaults): the call
may omit trailing defaulted arguments, so the hypothesis is the arity
*window* `arityOk f.params args.size` rather than exact arity; the entry
state binds the omitted parameters to their literal defaults. At a literal
module and literal `args` the window hypothesis closes by `rfl` (it
computes), which is how `py_vcgen` discharges it. -/
theorem PyTriple.callsTo_arityOk {m : Module} {fname : String}
    {f : FunctionDefn} {args : Array Val} {v : Val}
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : arityOk f.params args.size = true)
    (h : PyTriple m (fun st => st = (⟨initWorld m, mkCallEnv f.params (RVal.thawArgs args)⟩ : FrameState)) f.body.toList
        { next := fun _ => v = .none, ret := fun rv _ => rv = RVal.thaw v }) :
    CallsTo m fname args v := by
  obtain ⟨r, t, hr, hrun⟩ := h.exec rfl
  have hrt := hrun t (Nat.le_refl t)
  cases r with
  | ok st' flow =>
    cases flow with
    | next =>
      have hv : v = .none := hr
      refine ⟨t + 1, ?_⟩
      unfold callFunction
      rw [callIn]
      simp [hf, hargsOk, hlocalsOk, harity, hrt, hv, RVal.freezeB]
    | ret rv =>
      have hv : rv = RVal.thaw v := hr
      refine ⟨t + 1, ?_⟩
      unfold callFunction
      rw [callIn]
      simp [hf, hargsOk, hlocalsOk, harity, hrt, hv, RVal.freezeB_thaw]
    | brk => exact hr.elim
    | cont => exact hr.elim
  | exn st' e => exact hr.elim
  | timeout => exact (PyPost.holds_ne_timeout hr rfl).elim
  | unsupported msg => exact hr.elim

/-- Triple → arrow, value side: a whole-body triple whose `ret` arm pins
`RVal.thaw v` (and whose `next` arm forces `v = None`, Python's
fall-off-the-end) yields `CallsTo m fname args v` — i.e.
`fname(args) ==> v`. Exact-arity corollary of `PyTriple.callsTo_arityOk`
(`arityOk_full`). -/
theorem PyTriple.callsTo {m : Module} {fname : String} {f : FunctionDefn}
    {args : Array Val} {v : Val}
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : args.size = f.params.size)
    (h : PyTriple m (fun st => st = (⟨initWorld m, mkCallEnv f.params (RVal.thawArgs args)⟩ : FrameState)) f.body.toList
        { next := fun _ => v = .none, ret := fun rv _ => rv = RVal.thaw v }) :
    CallsTo m fname args v :=
  PyTriple.callsTo_arityOk hf hargsOk hlocalsOk
    (by rw [harity]; exact arityOk_full f.params) h

/-- Triple → arrow, `PyPost.ofRet` corollary of the general-arity form:
for bodies that always `return` explicitly, the function-body shape
`PyPost.ofRet` suffices — its `next := False` arm entails the general
bridge's `next` arm vacuously. -/
theorem PyTriple.callsTo_ofRet_arityOk {m : Module} {fname : String}
    {f : FunctionDefn} {args : Array Val} {v : Val}
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : arityOk f.params args.size = true)
    (h : PyTriple m (fun st => st = (⟨initWorld m, mkCallEnv f.params (RVal.thawArgs args)⟩ : FrameState)) f.body.toList
        (.ofRet fun rv _ => rv = RVal.thaw v)) :
    CallsTo m fname args v :=
  PyTriple.callsTo_arityOk hf hargsOk hlocalsOk harity
    (h.consequence (fun _ hp => hp)
      { next := fun _ hfalse => hfalse.elim
        ret := fun _ _ hw => hw
        brk := fun _ hfalse => hfalse.elim
        cont := fun _ hfalse => hfalse.elim
        err := fun _ _ hfalse => hfalse.elim })

/-- Triple → arrow, `PyPost.ofRet` corollary, exact arity. -/
theorem PyTriple.callsTo_ofRet {m : Module} {fname : String}
    {f : FunctionDefn} {args : Array Val} {v : Val}
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : args.size = f.params.size)
    (h : PyTriple m (fun st => st = (⟨initWorld m, mkCallEnv f.params (RVal.thawArgs args)⟩ : FrameState)) f.body.toList
        (.ofRet fun rv _ => rv = RVal.thaw v)) :
    CallsTo m fname args v :=
  PyTriple.callsTo_ofRet_arityOk hf hargsOk hlocalsOk
    (by rw [harity]; exact arityOk_full f.params) h

/-- Arrow → triple, value side: from `fname(args) ==> v` recover the
whole-body triple (guards derived from the successful run — no
`argsOk`/arity hypotheses needed; the wrapper's freeze is inverted by
`RVal.eq_thaw_of_freeze`). This is what lets a proof *assume* a callee's
arrow spec and keep working in the triple vocabulary. -/
theorem CallsTo.toTriple {m : Module} {fname : String} {f : FunctionDefn}
    {args : Array Val} {v : Val}
    (hf : findFunction m fname = some f)
    (h : CallsTo m fname args v)
    (hv : Val.listFree v = true := by first | rfl | decide) :
    PyTriple m (fun st => st = (⟨initWorld m, mkCallEnv f.params (RVal.thawArgs args)⟩ : FrameState)) f.body.toList
      { next := fun _ => v = .none, ret := fun rv _ => rv = RVal.thaw v } := by
  obtain ⟨fuel, hc⟩ := h
  unfold callFunction at hc
  cases fuel with
  | zero => rw [callIn] at hc; simp at hc
  | succ fu =>
    rw [callIn] at hc
    simp only [hf] at hc
    cases hao : f.argsOk with
    | false => simp [hao] at hc
    | true =>
    cases hlo : f.localsOk with
    | false => simp [hao, hlo] at hc
    | true =>
    simp only [RVal.thawArgs_size] at hc
    cases har : arityOk f.params args.size with
    | false => simp [hao, hlo, har] at hc
    | true =>
    simp only [hao, hlo, har, Bool.not_true, Bool.false_eq_true, if_false] at hc
    cases hex : execStmts m fu ((⟨initWorld m, mkCallEnv f.params (RVal.thawArgs args)⟩ : FrameState)) f.body.toList with
    | ok st1 flow =>
      rw [hex] at hc
      cases flow with
      | next =>
        simp only [Run.ok_bind, Run.toWorld_ok] at hc
        have hvn : v = .none := by
          have hcn : Run.toPublic (fu + 1)
              (Run.ok st1.world (RVal.thaw Val.none)) = .ok v := hc
          rw [Run.toPublic_thaw] at hcn
          exact (Res.ok.inj hcn).symm
        refine PyTriple.of_exec fun st hst => ⟨fu, ?_⟩
        subst hst
        rw [hex]
        simpa using hvn
      | ret rv =>
        simp only [Run.ok_bind, Run.toWorld_ok] at hc
        have hrv : rv = RVal.thaw v := by
          rw [Run.toPublic_ok] at hc
          exact RVal.eq_thaw_of_freezeB st1.world.heap (fu + 1) rv hc hv
        refine PyTriple.of_exec fun st hst => ⟨fu, ?_⟩
        subst hst
        rw [hex]
        simpa using hrv
      | brk => simp at hc
      | cont => simp at hc
    | exn st1 e => rw [hex] at hc; simp at hc
    | timeout => rw [hex] at hc; simp at hc
    | unsupported msg => rw [hex] at hc; simp at hc

/-- **The value-side bridge**, both directions: `fname(args) ==> v`
(`CallsTo`, also the elaboration of `⇓`) iff the whole-function triple. -/
theorem callsTo_iff_triple {m : Module} {fname : String} {f : FunctionDefn}
    {args : Array Val} {v : Val}
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : args.size = f.params.size)
    (hv : Val.listFree v = true := by first | rfl | decide) :
    CallsTo m fname args v ↔
      PyTriple m (fun st => st = (⟨initWorld m, mkCallEnv f.params (RVal.thawArgs args)⟩ : FrameState)) f.body.toList
        { next := fun _ => v = .none, ret := fun rv _ => rv = RVal.thaw v } :=
  ⟨fun h => h.toTriple hf hv, fun h => h.callsTo hf hargsOk hlocalsOk harity⟩

/-- Triple → arrow, raise side, general-arity form (F1 defaults). The
`err` arm is state-aware (the raise state survives INSIDE the run), but
the public boundary erases it (`Res.exn` carries no state), so the arm
spec here is state-agnostic: `fun e' _ => e' = e`. -/
theorem PyTriple.raises_arityOk {m : Module} {fname : String}
    {f : FunctionDefn} {args : Array Val} {e : PyErr}
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : arityOk f.params args.size = true)
    (h : PyTriple m (fun st => st = (⟨initWorld m, mkCallEnv f.params (RVal.thawArgs args)⟩ : FrameState)) f.body.toList
        { next := fun _ => False, err := fun e' _ => e' = e }) :
    Raises m fname args e := by
  obtain ⟨r, t, hr, hrun⟩ := h.exec rfl
  have hrt := hrun t (Nat.le_refl t)
  cases r with
  | ok st' flow =>
    cases flow with
    | next => exact hr.elim
    | ret w => exact hr.elim
    | brk => exact hr.elim
    | cont => exact hr.elim
  | exn st' e' =>
    have he : e' = e := hr
    refine ⟨t + 1, ?_⟩
    unfold callFunction
    rw [callIn]
    simp [hf, hargsOk, hlocalsOk, harity, hrt, he]
  | timeout => exact (PyPost.holds_ne_timeout hr rfl).elim
  | unsupported msg => exact hr.elim

/-- Triple → arrow, raise side: a whole-body triple landing in the `err`
arm at `e` yields `fname(args) ==>! e` — the `err` arm cashing out. -/
theorem PyTriple.raises {m : Module} {fname : String} {f : FunctionDefn}
    {args : Array Val} {e : PyErr}
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : args.size = f.params.size)
    (h : PyTriple m (fun st => st = (⟨initWorld m, mkCallEnv f.params (RVal.thawArgs args)⟩ : FrameState)) f.body.toList
        { next := fun _ => False, err := fun e' _ => e' = e }) :
    Raises m fname args e :=
  PyTriple.raises_arityOk hf hargsOk hlocalsOk
    (by rw [harity]; exact arityOk_full f.params) h

/-- Arrow → triple, raise side. Unlike `CallsTo.toTriple` the guard
hypotheses are required: an `.exn` result could otherwise be the arity
`TypeError` (or a name error) rather than a body raise. `freeze_ne_exn`
pins the raise to the run, never to the wrapper's freeze. -/
theorem Raises.toTriple {m : Module} {fname : String} {f : FunctionDefn}
    {args : Array Val} {e : PyErr}
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : args.size = f.params.size)
    (h : Raises m fname args e) :
    PyTriple m (fun st => st = (⟨initWorld m, mkCallEnv f.params (RVal.thawArgs args)⟩ : FrameState)) f.body.toList
      { next := fun _ => False, err := fun e' _ => e' = e } := by
  obtain ⟨fuel, hc⟩ := h
  unfold callFunction at hc
  cases fuel with
  | zero => rw [callIn] at hc; simp at hc
  | succ fu =>
    rw [callIn] at hc
    have har : arityOk f.params args.size = true := by
      rw [harity]; exact arityOk_full f.params
    simp only [RVal.thawArgs_size] at hc
    simp only [hf, hargsOk, hlocalsOk, har, Bool.not_true,
               Bool.false_eq_true, if_false] at hc
    cases hex : execStmts m fu ((⟨initWorld m, mkCallEnv f.params (RVal.thawArgs args)⟩ : FrameState)) f.body.toList with
    | ok st1 flow =>
      rw [hex] at hc
      cases flow with
      | next =>
        simp only [Run.ok_bind, Run.toWorld_ok] at hc
        exact absurd hc Run.toPublic_ok_ne_exn
      | ret rv =>
        simp only [Run.ok_bind, Run.toWorld_ok] at hc
        exact absurd hc Run.toPublic_ok_ne_exn
      | brk => simp at hc
      | cont => simp at hc
    | exn st1 e' =>
      rw [hex] at hc
      simp only [Run.exn_bind, Run.toWorld_exn] at hc
      have he : e' = e := (Res.exn.inj hc)
      subst he
      refine PyTriple.of_exec fun st hst => ⟨fu, ?_⟩
      subst hst
      rw [hex]
      exact rfl
    | timeout => rw [hex] at hc; simp at hc
    | unsupported msg => rw [hex] at hc; simp at hc

/-- **The raise-side bridge**, both directions: `fname(args) ==>! e`
(`Raises`) iff the whole-function triple through the `err` arm. -/
theorem raises_iff_triple {m : Module} {fname : String} {f : FunctionDefn}
    {args : Array Val} {e : PyErr}
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : args.size = f.params.size) :
    Raises m fname args e ↔
      PyTriple m (fun st => st = (⟨initWorld m, mkCallEnv f.params (RVal.thawArgs args)⟩ : FrameState)) f.body.toList
        { next := fun _ => False, err := fun e' _ => e' = e } :=
  ⟨fun h => h.toTriple hf hargsOk hlocalsOk harity,
   fun h => h.raises hf hargsOk hlocalsOk harity⟩

/-! ## Smoke tests

Two hand-built loops proved through `PyStmtTriple.whileLoop` alone, with
`#guard`s pinning the concrete runs (non-vacuity): a countdown (normal
test-false exit) and a `while 1: break` (break-exit unified into `next`).
Both are parametric in the pinned world `w` — the loop rules never touch
it. The interprocedural rules and bridges are smoke-tested by the
recursion pattern in VCTests.lean, which needs a module literal. -/

section SmokeTest

private abbrev wSp : Span := ⟨0, 0, 0, 0⟩
/-- `while x: x = x - 1` (int truthiness as the test). -/
private abbrev wLoop : Stmt :=
  .whileLoop (.name "x" wSp)
    #[.assign #[.name "x" wSp]
        (.binOp (.name "x" wSp) .sub (.constant (.int 1) wSp) wSp) wSp]
    #[] wSp

#guard execStmt ⟨#[], #[], #[]⟩ 64 ⟨⟨#[], [], []⟩, [("x", .int 5)]⟩ wLoop
  == .ok ⟨⟨#[], [], []⟩, [("x", .int 0)]⟩ .next

/-- The countdown terminates at `x = 0` — while rule only, any module,
any pinned world. -/
example (m : Module) (w : World) :
    PyStmtTriple m (fun st => ∃ n : Nat, st = ⟨w, [("x", .int n)]⟩) wLoop
      (.ofNext fun st => st = ⟨w, [("x", .int 0)]⟩) := by
  refine .whileLoop (fun st => ∃ n : Nat, st = ⟨w, [("x", .int n)]⟩)
      (fun st => match Env.lookup st.locals "x" with
        | some (.int i) => i.toNat | _ => 0)
      (fun st => (Env.lookup st.locals "x").getD .none) ?_ ?_ ?_ ?_
  · rintro st ⟨n, rfl⟩
    exact ⟨1, rfl⟩
  · rintro st ⟨n, rfl⟩
    exact ⟨_, rfl⟩
  · rintro st ⟨n, rfl⟩ hfalse
    simp [Env.lookup, truthy] at hfalse
    simp [PyPost.ofNext, hfalse]
  · intro k
    refine PyTriple.single (.assignName ?_)
    rintro st ⟨⟨n, rfl⟩, htrue, hk⟩
    simp [Env.lookup, truthy] at htrue
    simp [Env.lookup] at hk
    refine ⟨.int (n - 1), .of_eval (fuel := 3) rfl, ⟨n - 1, ?_⟩, ?_⟩
    · simp [Env.set]
      omega
    · simp [Env.set, Env.lookup]
      omega

/-- `while 1: break` — the `brk` arm exits straight into `Q.next`. -/
example (m : Module) (w : World) :
    PyStmtTriple m (fun st => st = ⟨w, []⟩)
      (.whileLoop (.constant (.int 1) wSp) #[.brk wSp] #[] wSp)
      (.ofNext fun st => st = ⟨w, []⟩) := by
  refine .whileLoop (fun st => st = ⟨w, []⟩) (fun _ => 0) (fun _ => .int 1)
    ?_ ?_ ?_ ?_
  · rintro st rfl
    exact ⟨1, rfl⟩
  · rintro st rfl
    exact ⟨true, by simp [truthy]⟩
  · rintro st rfl h
    simp [truthy] at h
  · intro k
    exact PyTriple.single (.brk fun st h => h.1)

end SmokeTest

end LeanModels.Python
