import LeanModels.Python.VC
import LeanModels.Python.Surface

/-!
# Control-flow and interprocedural rules (`py_vcgen` layer 2)

Layer 1 (VC.lean) built the flow-aware triples (`PyPost`/`PyStmtTriple`/
`PyTriple`) and the straight-line rules; this file adds the rules that
*consume* the `brk`/`cont`/`ret` arms layer 1 plumbed, plus the bridges that
connect triples to the arrow surface (Surface.lean). Everything is additive:
`execWhile_total_of_invariant` and `py_loop` are untouched.

* **`PyStmtTriple.whileLoop`** — THE loop rule, generalizing
  `execWhile_total_of_invariant` (Surface.lean) into the triple vocabulary:
  invariant `Inv : Env → Prop` (directly on interpreter environments — no
  `σ`/`toEnv` rendering layer), measure `μ : Env → Nat`, test-value function
  `tv : Env → Val` (kept as an explicit function, the Miller-pattern shape a
  future vcgen derives by unification, exactly as `py_loop` derives the old
  rule's `tv`/`Cont`/`step`). The body triple's post arms route Python's
  loop flow: `next`/`cont` re-establish the invariant with a smaller
  measure (`continue` re-tests, so it is an iteration like any other),
  `brk` lands directly in the *loop's* `Q.next` (Python `break` skips
  `orelse`; with `orelse = []` normal exit also lands in `next`, so the two
  exits unify), `ret` propagates to the outer `Q.ret` (a `return` inside
  the loop escapes the whole function body), `err` propagates to `Q.err`.
  Restriction (documented, deliberate): the rule covers `orelse = #[]` only
  — orelse-carrying specs would need a separate orelse triple run on the
  normal exit *but not* the `break` exit, and no gallery loop has an
  `orelse`; add the extra hypothesis when one does. The engine is
  `execWhile_of_invariant` (strong induction on the measure, the
  `execWhile_total_of_invariant` recipe re-proved against `PyPost.holds`);
  the old rule remains the `py_loop` backend — this rule is what the vcgen
  tactic will target.

* **Interprocedural rules** — `EvalsToList` (the `evalExprs` analog of
  `EvalsTo`, with `nil`/`cons` introductions so argument lists compose from
  per-argument facts), `EvalsTo.call` (the compositional primitive: a call
  *expression* evaluates to `v` given a `CallsTo` fact for the callee at
  the argument values — any `CallsTo` fact: a `@[py_spec]` lemma
  instantiated by hand or by the future vcgen, or a *local hypothesis*,
  e.g. the induction hypothesis of a recursion proof; the rule is
  explicit-hypothesis-based precisely so local IHs work), and
  `PyStmtTriple.call`/`PyTriple.call` (`x = f(e₁, …, eₖ)` binds the callee's
  result in `Q.next`). A call in another position (`return f(x)`,
  `y = 1 + f(x)`) needs no extra statement rule: splice `EvalsTo.call`
  into the corresponding `EvalsTo` hypothesis.

* **The `@[py_spec]` registry** — the concrete registry story for callee
  specs: `@[py_spec]` marks a lemma whose conclusion (after its binders and
  precondition hypotheses) is **`CallsTo`-shaped** (surface arrow form,
  `f(a, b) ==> v` — exactly the statements spec.lean files already export).
  CallsTo-based rather than PyTriple-based was the settled fork: spec.lean
  statements stay in arrow form verbatim, and the bridge theorems below
  translate to/from triples whenever a proof wants to go through the triple
  layer. The attribute is a plain label (core `register_label_attr`):
  retrieval is `Lean.labelled `py_spec` (CoreM) — the future vcgen looks a
  callee's spec up there and instantiates it; the *rules* take the
  resulting `CallsTo` fact as an ordinary explicit hypothesis, so
  attribute-registered and local specs are consumed identically.

* **Bridge theorems** (what Acceptance uses to migrate proofs while
  keeping every spec.lean statement unchanged): `callsTo_iff_triple` —
  `f(args) ==> v` (`CallsTo`, i.e. also `⇓`) *iff* the whole-function-body
  triple from entry env `mkCallEnv f.params args` with `Q.ret` as the
  return spec (and the `next` arm covering Python's implicit `return
  None`); directional forms `PyTriple.callsTo` / `CallsTo.toTriple`, the
  `PyPost.ofRet` corollary `PyTriple.callsTo_ofRet` for bodies that always
  return explicitly, and the raise-side pair `PyTriple.raises` /
  `Raises.toTriple` / `raises_iff_triple` (`==>!` through the `err` arm —
  the arm layer 1 paid for, cashing out). The `findFunction`/`argsOk`/
  `localsOk`/arity side hypotheses are discharged by `rfl`/`py_simp` at
  concrete modules.

Recursion pattern (proved in VCTests.lean, the scheme recorded here):
induct on the *math* variable (house rule — never on fuel); in the step
case the IH is a local `CallsTo` fact at the smaller argument, consumed by
`PyStmtTriple.call`/`EvalsTo.call` exactly as a registered spec would be;
close the case through `PyTriple.callsTo`. No fixpoint rule is needed —
`CallsTo`'s `∃ fuel` does the tying, `fuelMono` the splicing.
-/

namespace LeanModels.Python

/-- Destructure a nonzero-threshold bound: `F ≥ t + 1` is a successor
`F' + 1` with `F' ≥ t` (private twin of VC.lean's helper). -/
private theorem succ_le_dest {t F : Nat} (h : t + 1 ≤ F) :
    ∃ F', F = F' + 1 ∧ t ≤ F' := ⟨F - 1, by omega, by omega⟩

/-! ## Argument lists: `EvalsToList` -/

/-- Terminating evaluation of an expression list (the `evalExprs` analog of
`EvalsTo`, same `∃ fuel` shape, same `at_least` accessor) — the
argument-vector interface of the call rules. Build it from per-argument
`EvalsTo` facts with `nil`/`cons`, or from one concrete run (`of_eval`). -/
def EvalsToList (m : Module) (env : Env) (es : List Expr) (vs : List Val) : Prop :=
  ∃ fuel, evalExprs m fuel env es = .ok vs

namespace EvalsToList

/-- Introduce `EvalsToList` from one concrete run (any fuel). -/
theorem of_eval {m : Module} {fuel : Nat} {env : Env} {es : List Expr}
    {vs : List Val} (h : evalExprs m fuel env es = .ok vs) :
    EvalsToList m env es vs := ⟨fuel, h⟩

/-- Fuel-threshold form (the `EvalsTo.at_least` analog, via `evalExprs_mono`). -/
theorem at_least {m : Module} {env : Env} {es : List Expr} {vs : List Val}
    (h : EvalsToList m env es vs) :
    ∃ t, ∀ F ≥ t, evalExprs m F env es = .ok vs := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, fun F hF => evalExprs_mono hf (by simp) F hF⟩

/-- The empty argument list. -/
theorem nil {m : Module} {env : Env} : EvalsToList m env [] [] := ⟨1, rfl⟩

/-- Prepend one evaluated argument (thresholds spliced at a summed bound). -/
theorem cons {m : Module} {env : Env} {e : Expr} {v : Val} {es : List Expr}
    {vs : List Val} (hv : EvalsTo m env e v) (hvs : EvalsToList m env es vs) :
    EvalsToList m env (e :: es) (v :: vs) := by
  obtain ⟨t1, h1⟩ := hv.at_least
  obtain ⟨t2, h2⟩ := hvs.at_least
  refine ⟨t1 + t2 + 1, ?_⟩
  simp [evalExprs, h1 (t1 + t2) (by omega), h2 (t1 + t2) (by omega)]

end EvalsToList

/-! ## The while rule -/

/-- The while rule's engine, at the `execWhile` level: from any invariant
environment some fuel threshold lands the whole loop in the arm `Q`
prescribes. Strong induction on the measure — the
`execWhile_total_of_invariant` recipe (Surface.lean) re-proved against
`PyPost.holds`, with the body's `brk`/`ret`/`err` escapes routed to `Q`'s
arms instead of being ruled out. `orelse = []` only (module docstring).
Instantiate directly (instead of via `PyStmtTriple.whileLoop`) when the
loop occurrence is already an `execWhile` term, e.g. after hand-unrolling
an iteration à la `Examples/python/rsa_inverse`. -/
theorem execWhile_of_invariant {m : Module} {test : Expr} {body : List Stmt}
    {Q : PyPost} (Inv : Env → Prop) (μ : Env → Nat) (tv : Env → Val)
    (htest : ∀ env, Inv env → EvalsTo m env test (tv env))
    (hexit : ∀ env, Inv env → truthy (tv env) = false → Q.next env)
    (hbody : ∀ n, PyTriple m
        (fun env => Inv env ∧ truthy (tv env) = true ∧ μ env = n) body
        { next := fun env' => Inv env' ∧ μ env' < n
          ret := Q.ret
          brk := Q.next
          cont := fun env' => Inv env' ∧ μ env' < n
          err := Q.err }) :
    ∀ env, Inv env → ∃ t, ∀ F ≥ t, Q.holds (execWhile m F env test body []) := by
  intro env hI
  generalize hn : μ env = n
  induction n using Nat.strongRecOn generalizing env with
  | ind n ih =>
    obtain ⟨tt, ht⟩ := (htest env hI).at_least
    cases hb : truthy (tv env)
    · -- test false: exit through the (empty) orelse into `Q.next`
      refine ⟨tt + 2, fun F hF => ?_⟩
      obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
      obtain ⟨F'', rfl, hF''⟩ := succ_le_dest hF'
      simpa [execWhile, ht (F'' + 1) (by omega), hb, execStmts]
        using hexit env hI hb
    · -- test true: run the body, dispatch on how it landed
      obtain ⟨r, tb, hr, hrun⟩ := (hbody n).exec ⟨hI, hb, hn⟩
      cases r with
      | ok p =>
        obtain ⟨env', flow⟩ := p
        cases flow with
        | next =>
          obtain ⟨hI', hlt⟩ := hr
          obtain ⟨tw, hw⟩ := ih (μ env') hlt env' hI' rfl
          have h0 := hw tw (Nat.le_refl tw)
          have hpin := execWhile_mono rfl (PyPost.holds_ne_timeout h0)
          refine ⟨tt + tb + tw + 1, fun F hF => ?_⟩
          obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
          rw [execWhile, ht F' (by omega)]
          simp only [Res.ok_bind, hb, if_true]
          rw [hrun F' (by omega)]
          simp only [Res.ok_bind]
          rw [hpin F' (by omega)]
          exact h0
        | cont =>
          -- `continue` re-tests: an iteration like `next` (same measure step)
          obtain ⟨hI', hlt⟩ := hr
          obtain ⟨tw, hw⟩ := ih (μ env') hlt env' hI' rfl
          have h0 := hw tw (Nat.le_refl tw)
          have hpin := execWhile_mono rfl (PyPost.holds_ne_timeout h0)
          refine ⟨tt + tb + tw + 1, fun F hF => ?_⟩
          obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
          rw [execWhile, ht F' (by omega)]
          simp only [Res.ok_bind, hb, if_true]
          rw [hrun F' (by omega)]
          simp only [Res.ok_bind]
          rw [hpin F' (by omega)]
          exact h0
        | brk =>
          -- `break` skips orelse: unified into the loop's `next` exit
          refine ⟨tt + tb + 1, fun F hF => ?_⟩
          obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
          rw [execWhile, ht F' (by omega)]
          simp only [Res.ok_bind, hb, if_true]
          rw [hrun F' (by omega)]
          simpa using hr
        | ret v =>
          -- `return` escapes the loop into the outer `ret` arm
          refine ⟨tt + tb + 1, fun F hF => ?_⟩
          obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
          rw [execWhile, ht F' (by omega)]
          simp only [Res.ok_bind, hb, if_true]
          rw [hrun F' (by omega)]
          simpa using hr
      | exn e =>
        refine ⟨tt + tb + 1, fun F hF => ?_⟩
        obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
        rw [execWhile, ht F' (by omega)]
        simp only [Res.ok_bind, hb, if_true]
        rw [hrun F' (by omega)]
        simpa using hr
      | timeout => exact (PyPost.holds_ne_timeout hr rfl).elim
      | unsupported msg => exact hr.elim

/-- **The while rule** — `execWhile_total_of_invariant` generalized to the
triple vocabulary (module docstring): from invariant `Inv` with measure `μ`
and test-value function `tv`, a body triple whose arms route Python's loop
flow — `next`/`cont`: invariant re-established, measure decreased; `brk`:
the loop's `Q.next` directly (break-exit unified with the normal
test-false exit, per Python `while` semantics with `orelse = []`); `ret`:
the outer `Q.ret`; `err`: `Q.err` — yields the loop statement's triple
from precondition `Inv` (strengthen with `PyStmtTriple.consequence`).
Restriction: `orelse = #[]` (orelse-carrying specs deferred — module
docstring). The old rule stays; `py_loop` still targets it. -/
theorem PyStmtTriple.whileLoop {m : Module} {test : Expr} {body : Array Stmt}
    {sp : Span} {Q : PyPost} (Inv : Env → Prop) (μ : Env → Nat) (tv : Env → Val)
    (htest : ∀ env, Inv env → EvalsTo m env test (tv env))
    (hexit : ∀ env, Inv env → truthy (tv env) = false → Q.next env)
    (hbody : ∀ n, PyTriple m
        (fun env => Inv env ∧ truthy (tv env) = true ∧ μ env = n) body.toList
        { next := fun env' => Inv env' ∧ μ env' < n
          ret := Q.ret
          brk := Q.next
          cont := fun env' => Inv env' ∧ μ env' < n
          err := Q.err }) :
    PyStmtTriple m Inv (.whileLoop test body #[] sp) Q := by
  intro env hI
  obtain ⟨t, ht⟩ := execWhile_of_invariant Inv μ tv htest hexit hbody env hI
  refine ⟨t + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  simpa [execStmt] using ht F' hF'

/-- List-level singleton form of the while rule (a loop standing alone as a
statement list — e.g. a whole function body); for a loop in mid-list
position feed `PyStmtTriple.whileLoop` to `PyTriple.seq` instead. -/
theorem PyTriple.whileLoop {m : Module} {test : Expr} {body : Array Stmt}
    {sp : Span} {Q : PyPost} (Inv : Env → Prop) (μ : Env → Nat) (tv : Env → Val)
    (htest : ∀ env, Inv env → EvalsTo m env test (tv env))
    (hexit : ∀ env, Inv env → truthy (tv env) = false → Q.next env)
    (hbody : ∀ n, PyTriple m
        (fun env => Inv env ∧ truthy (tv env) = true ∧ μ env = n) body.toList
        { next := fun env' => Inv env' ∧ μ env' < n
          ret := Q.ret
          brk := Q.next
          cont := fun env' => Inv env' ∧ μ env' < n
          err := Q.err }) :
    PyTriple m Inv [.whileLoop test body #[] sp] Q :=
  PyTriple.single (PyStmtTriple.whileLoop Inv μ tv htest hexit hbody)

/-! ## Interprocedural rules -/

/-- A call *expression* evaluates to the callee's result: the compositional
primitive behind `PyStmtTriple.call`, and the splice point for calls in any
other expression position (`return f(x)`, operands). Hypotheses: the callee
name is not shadowed by a local binding (else the call raises `TypeError`),
the arguments evaluate (`EvalsToList`), and a `CallsTo` fact — a
`@[py_spec]` lemma instantiated at the argument values, or a *local*
hypothesis such as a recursion proof's IH — gives the callee's result. The
`findFunction` lookup is *derived* from the `CallsTo` fact, not assumed. -/
theorem EvalsTo.call {m : Module} {env : Env} {fname : String}
    {args : Array Expr} {vs : List Val} {v : Val} {sp sp' : Span}
    (hlocal : Env.lookup env fname = Option.none)
    (hargs : EvalsToList m env args.toList vs)
    (hspec : CallsTo m fname vs.toArray v) :
    EvalsTo m env (.call (.name fname sp) args Option.none sp') v := by
  obtain ⟨ta, ha⟩ := hargs.at_least
  obtain ⟨tc, hc⟩ := hspec.at_least
  have hfn : (findFunction m fname).isSome = true := by
    have h1 := hc (tc + 1) (by omega)
    rw [callFunction] at h1
    cases hff : findFunction m fname with
    | none => rw [hff] at h1; simp at h1
    | some f => simp
  refine ⟨ta + tc + 1, ?_⟩
  simp [evalExpr, hlocal, hfn, ha (ta + tc) (by omega), hc (ta + tc) (by omega)]

/-- **The call rule** — `x = f(e₁, …, eₖ)` consuming a callee spec: from
each `P`-environment, the callee name unshadowed, argument values
(`EvalsToList`, built by `.cons`/`.nil` from per-argument `EvalsTo`), a
`CallsTo` fact at those values (registered `@[py_spec]` lemma or local
hypothesis — module docstring), and `Q.next` at the result bound to `x`.
Derived: `assignName` ∘ `EvalsTo.call`, no interpreter work. -/
theorem PyStmtTriple.call {m : Module} {P : Env → Prop} {Q : PyPost}
    {x fname : String} {args : Array Expr} {spx spf spc spa : Span}
    (h : ∀ env, P env → Env.lookup env fname = Option.none ∧
        ∃ vs v, EvalsToList m env args.toList vs ∧
          CallsTo m fname vs.toArray v ∧ Q.next (Env.set env x v)) :
    PyStmtTriple m P
      (.assign #[.name x spx] (.call (.name fname spf) args Option.none spc) spa)
      Q :=
  PyStmtTriple.assignName fun env hP =>
    let ⟨hlocal, _vs, v, hvs, hc, hQ⟩ := h env hP
    ⟨v, EvalsTo.call hlocal hvs hc, hQ⟩

/-- List-level form of the call rule: `x = f(…)` followed by `rest`, with
the callee's postcondition (result bound to `x`) as the midcondition `R`. -/
theorem PyTriple.call {m : Module} {P R : Env → Prop} {Q : PyPost}
    {x fname : String} {args : Array Expr} {spx spf spc spa : Span}
    {rest : List Stmt}
    (h : ∀ env, P env → Env.lookup env fname = Option.none ∧
        ∃ vs v, EvalsToList m env args.toList vs ∧
          CallsTo m fname vs.toArray v ∧ R (Env.set env x v))
    (hrest : PyTriple m R rest Q) :
    PyTriple m P
      (.assign #[.name x spx] (.call (.name fname spf) args Option.none spc) spa
        :: rest) Q :=
  PyTriple.seq (PyStmtTriple.call h) hrest

/-! ## The `@[py_spec]` registry -/

/-- Marks a callee specification for the py_vcgen layer. Required shape:
after the lemma's binders and precondition hypotheses, the conclusion is
`CallsTo`-shaped — surface arrow form, `f(a, b) ==> v` (the form spec.lean
files already export; `⇓` elaborates to the same `CallsTo`). Retrieval:
`Lean.labelled `py_spec` (CoreM). The call rules consume the instantiated
`CallsTo` fact as an ordinary hypothesis, so registered lemmas and local
hypotheses (e.g. a recursion IH) are interchangeable; to move between this
arrow form and the triple layer use `callsTo_iff_triple`. Distinct from
core's `@[spec]` (the mvcgen registry the raw ∀-fuel corollaries use) —
`@[py_spec]` is the *arrow-form* registry of this DSL's vcgen. -/
register_label_attr py_spec

/-! ## Bridges: triples ⇄ the arrow surface

Whole-function bridges — entry environment `mkCallEnv f.params args`,
`Q.ret` as the return spec, the `next` arm as Python's implicit
`return None`. These keep every spec.lean statement in arrow form while
proofs go through triples (`==>`/`⇓` are notation for `CallsTo`; `==>!`
for `Raises`). Side hypotheses (`findFunction`/`argsOk`/`localsOk`/arity)
close by `rfl`/`py_simp` at concrete modules; the backward `CallsTo`
direction *derives* the guards from the successful run instead. -/

/-- Triple → arrow, value side: a whole-body triple whose `ret` arm pins
`v` (and whose `next` arm forces `v = None`, Python's fall-off-the-end)
yields `CallsTo m fname args v` — i.e. `fname(args) ==> v`. -/
theorem PyTriple.callsTo {m : Module} {fname : String} {f : FunctionDefn}
    {args : Array Val} {v : Val}
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : args.size = f.params.size)
    (h : PyTriple m (fun env => env = mkCallEnv f.params args) f.body.toList
        { next := fun _ => v = .none, ret := fun w _ => w = v }) :
    CallsTo m fname args v := by
  obtain ⟨r, t, hr, hrun⟩ := h.exec rfl
  have hrt := hrun t (Nat.le_refl t)
  cases r with
  | ok p =>
    obtain ⟨env', flow⟩ := p
    cases flow with
    | next =>
      have hv : v = .none := hr
      refine ⟨t + 1, ?_⟩
      rw [callFunction, hf]
      simp [hargsOk, hlocalsOk, harity, hrt, hv]
    | ret w =>
      have hv : w = v := hr
      refine ⟨t + 1, ?_⟩
      rw [callFunction, hf]
      simp [hargsOk, hlocalsOk, harity, hrt, hv]
    | brk => exact hr.elim
    | cont => exact hr.elim
  | exn e => exact hr.elim
  | timeout => exact (PyPost.holds_ne_timeout hr rfl).elim
  | unsupported msg => exact hr.elim

/-- Triple → arrow, `PyPost.ofRet` corollary: for bodies that always
`return` explicitly (every gallery function), the function-body shape
`PyPost.ofRet` suffices — its `next := False` arm entails the general
bridge's `next` arm vacuously. -/
theorem PyTriple.callsTo_ofRet {m : Module} {fname : String}
    {f : FunctionDefn} {args : Array Val} {v : Val}
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : args.size = f.params.size)
    (h : PyTriple m (fun env => env = mkCallEnv f.params args) f.body.toList
        (.ofRet fun w _ => w = v)) :
    CallsTo m fname args v :=
  PyTriple.callsTo hf hargsOk hlocalsOk harity
    (h.consequence (fun _ hp => hp)
      { next := fun _ hfalse => hfalse.elim
        ret := fun _ _ hw => hw
        brk := fun _ hfalse => hfalse.elim
        cont := fun _ hfalse => hfalse.elim
        err := fun _ hfalse => hfalse.elim })

/-- Arrow → triple, value side: from `fname(args) ==> v` recover the
whole-body triple (guards derived from the successful run — no
`argsOk`/arity hypotheses needed). This is what lets a proof *assume* a
callee's arrow spec and keep working in the triple vocabulary. -/
theorem CallsTo.toTriple {m : Module} {fname : String} {f : FunctionDefn}
    {args : Array Val} {v : Val}
    (hf : findFunction m fname = some f)
    (h : CallsTo m fname args v) :
    PyTriple m (fun env => env = mkCallEnv f.params args) f.body.toList
      { next := fun _ => v = .none, ret := fun w _ => w = v } := by
  obtain ⟨fuel, hc⟩ := h
  cases fuel with
  | zero => simp [callFunction] at hc
  | succ fu =>
    simp only [callFunction, hf] at hc
    cases hao : f.argsOk with
    | false => rw [hao] at hc; simp at hc
    | true =>
    cases hlo : f.localsOk with
    | false => rw [hao, hlo] at hc; simp at hc
    | true =>
    rw [hao, hlo] at hc
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at hc
    by_cases har : args.size = f.params.size
    case neg =>
      rw [if_pos (show args.size ≠ f.params.size from har)] at hc
      simp at hc
    case pos =>
      rw [if_neg (show ¬args.size ≠ f.params.size from fun hne => hne har)] at hc
      rw [Res.bind_eq_ok] at hc
      obtain ⟨⟨env', flow⟩, hex, hflow⟩ := hc
      cases flow with
      | next =>
        simp at hflow
        refine PyTriple.of_exec fun env henv => ⟨fu, ?_⟩
        subst henv
        rw [hex]
        exact hflow.symm
      | ret w =>
        simp at hflow
        refine PyTriple.of_exec fun env henv => ⟨fu, ?_⟩
        subst henv
        rw [hex]
        exact hflow
      | brk => simp at hflow
      | cont => simp at hflow

/-- **The value-side bridge**, both directions: `fname(args) ==> v`
(`CallsTo`, also the elaboration of `⇓`) iff the whole-function triple. -/
theorem callsTo_iff_triple {m : Module} {fname : String} {f : FunctionDefn}
    {args : Array Val} {v : Val}
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : args.size = f.params.size) :
    CallsTo m fname args v ↔
      PyTriple m (fun env => env = mkCallEnv f.params args) f.body.toList
        { next := fun _ => v = .none, ret := fun w _ => w = v } :=
  ⟨fun h => h.toTriple hf, fun h => h.callsTo hf hargsOk hlocalsOk harity⟩

/-- Triple → arrow, raise side: a whole-body triple landing in the `err`
arm at `e` yields `fname(args) ==>! e` — the `err` arm cashing out. -/
theorem PyTriple.raises {m : Module} {fname : String} {f : FunctionDefn}
    {args : Array Val} {e : PyErr}
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : args.size = f.params.size)
    (h : PyTriple m (fun env => env = mkCallEnv f.params args) f.body.toList
        { next := fun _ => False, err := fun e' => e' = e }) :
    Raises m fname args e := by
  obtain ⟨r, t, hr, hrun⟩ := h.exec rfl
  have hrt := hrun t (Nat.le_refl t)
  cases r with
  | ok p =>
    obtain ⟨env', flow⟩ := p
    cases flow with
    | next => exact hr.elim
    | ret w => exact hr.elim
    | brk => exact hr.elim
    | cont => exact hr.elim
  | exn e' =>
    have he : e' = e := hr
    refine ⟨t + 1, ?_⟩
    rw [callFunction, hf]
    simp [hargsOk, hlocalsOk, harity, hrt, he]
  | timeout => exact (PyPost.holds_ne_timeout hr rfl).elim
  | unsupported msg => exact hr.elim

/-- Arrow → triple, raise side. Unlike `CallsTo.toTriple` the guard
hypotheses are required: an `.exn` result could otherwise be the arity
`TypeError` (or a name error) rather than a body raise. -/
theorem Raises.toTriple {m : Module} {fname : String} {f : FunctionDefn}
    {args : Array Val} {e : PyErr}
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : args.size = f.params.size)
    (h : Raises m fname args e) :
    PyTriple m (fun env => env = mkCallEnv f.params args) f.body.toList
      { next := fun _ => False, err := fun e' => e' = e } := by
  obtain ⟨fuel, hc⟩ := h
  cases fuel with
  | zero => simp [callFunction] at hc
  | succ fu =>
    simp only [callFunction, hf] at hc
    rw [hargsOk, hlocalsOk] at hc
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at hc
    rw [if_neg (show ¬args.size ≠ f.params.size from fun hne => hne harity)] at hc
    cases hex : execStmts m fu (mkCallEnv f.params args) f.body.toList with
    | ok p =>
      obtain ⟨env', flow⟩ := p
      rw [hex] at hc
      cases flow <;> simp at hc
    | exn e' =>
      rw [hex] at hc
      simp at hc
      subst hc
      exact PyTriple.of_exec fun env henv => ⟨fu, by subst henv; rw [hex]; exact rfl⟩
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
      PyTriple m (fun env => env = mkCallEnv f.params args) f.body.toList
        { next := fun _ => False, err := fun e' => e' = e } :=
  ⟨fun h => h.toTriple hf hargsOk hlocalsOk harity,
   fun h => h.raises hf hargsOk hlocalsOk harity⟩

/-! ## Smoke tests

Two hand-built loops proved through `PyStmtTriple.whileLoop` alone, with
`#guard`s pinning the concrete runs (non-vacuity): a countdown (normal
test-false exit) and a `while 1: break` (break-exit unified into `next`).
The interprocedural rules and bridges are smoke-tested by the recursion
pattern in VCTests.lean, which needs a module literal. -/

section SmokeTest

private abbrev wSp : Span := ⟨0, 0, 0, 0⟩
/-- `while x: x = x - 1` (int truthiness as the test). -/
private abbrev wLoop : Stmt :=
  .whileLoop (.name "x" wSp)
    #[.assign #[.name "x" wSp]
        (.binOp (.name "x" wSp) .sub (.constant (.int 1) wSp) wSp) wSp]
    #[] wSp

#guard execStmt ⟨#[], #[]⟩ 64 [("x", .int 5)] wLoop == .ok ([("x", .int 0)], .next)

/-- The countdown terminates at `x = 0` — while rule only, any module. -/
example (m : Module) :
    PyStmtTriple m (fun env => ∃ n : Nat, env = [("x", .int n)]) wLoop
      (.ofNext fun env => env = [("x", .int 0)]) := by
  refine .whileLoop (fun env => ∃ n : Nat, env = [("x", .int n)])
      (fun env => match Env.lookup env "x" with | some (.int i) => i.toNat | _ => 0)
      (fun env => (Env.lookup env "x").getD .none) ?_ ?_ ?_
  · rintro env ⟨n, rfl⟩
    exact ⟨1, rfl⟩
  · rintro env ⟨n, rfl⟩ hfalse
    simp [Env.lookup, truthy] at hfalse
    simp [PyPost.ofNext, hfalse]
  · intro k
    refine PyTriple.single (.assignName ?_)
    rintro env ⟨⟨n, rfl⟩, htrue, hk⟩
    simp [Env.lookup, truthy] at htrue
    simp [Env.lookup] at hk
    refine ⟨.int (n - 1), .of_eval (fuel := 3) rfl, ⟨n - 1, ?_⟩, ?_⟩
    · simp [Env.set]
      omega
    · simp [Env.set, Env.lookup]
      omega

/-- `while 1: break` — the `brk` arm exits straight into `Q.next`. -/
example (m : Module) :
    PyStmtTriple m (fun env => env = [])
      (.whileLoop (.constant (.int 1) wSp) #[.brk wSp] #[] wSp)
      (.ofNext fun env => env = []) := by
  refine .whileLoop (fun env => env = []) (fun _ => 0) (fun _ => .int 1) ?_ ?_ ?_
  · rintro env rfl
    exact ⟨1, rfl⟩
  · rintro env rfl h
    simp [truthy] at h
  · intro k
    exact PyTriple.single (.brk fun env h => h.1)

end SmokeTest

end LeanModels.Python
