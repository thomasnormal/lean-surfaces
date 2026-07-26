import LeanModels.Python.VC2
import LeanModels.Python.LoopTactic

/-!
# `py_vcgen` — the VC-generating walker (py_vcgen layer 3)

The tactic that turns the layer-1/2 rules (VC.lean/VC2.lean) into a proof
*surface*: from a `f(args) ==> v` (`CallsTo`) goal — or a `PyTriple` goal
whose precondition is `fun env => env = <literal>` — it bridges to the
whole-function-body triple (`PyTriple.callsTo`) and walks the statement list,
applying the structural rules and discharging every interpreter obligation by
captured symbolic execution, so that only mathematics remains.

Surface:

* `py_vcgen [prog]` / `py_vcgen [prog, aux…]` (extra idents are additional
  constants to unfold during captured runs — hand-built `FunctionDefn`
  constants of test modules) — walk with no loop clauses: each loop's
  invariant and measure are left as *delayed goals* (mvcgen-style): for the i-th loop in
  source order, goals `case inv<i> ⊢ Int → ⋯ → Prop` and
  `case dec<i> ⊢ Int → ⋯ → Nat` (over the loop's *assigned* variables, in
  environment order) come first; assigning them instantiates the math
  residuals that mention them. A `break`-carrying loop additionally gets
  `case exit<i> ⊢ Int → ⋯ → Prop` (same binders) — the exit-clause request
  the clause form takes as `(exit<i> := …)`; without it the loop's exit
  fact would silently weaken to the bare invariant.
* `py_vcgen [prog] (inv := fun (x y : Int) => …) (dec := fun (x y : Int) => …)`
  — clause form: the i-th `(inv := …) (dec := …)` pair belongs to the i-th
  `while` in source order (any label starting with `inv` resp. `dec` works:
  `inv1`, `dec1`, …; loops are indexed by a pre-scan, so an `if`-fork that
  reaches the same loop twice consumes the same pair twice). Binder names
  must be the Python names of variables **assigned in that loop's body** and
  present at loop entry (they select the environment slots, exactly as
  `py_loop`); unassigned variables stay pinned to their current symbolic
  values, so the invariant refers to them directly (`n` in `tri`, `oa`/`ob`
  in `extended_gcd` need no clause mention). A clause for an inner loop is
  elaborated *at its loop's program point*, so it may also refer to the
  enclosing loops' variables by name. An optional `(exit<i> := fun (x…) => P)`
  clause (index = loop number, default 1; binders a subset of that loop's
  `inv` binders) states the i-th loop's exit fact explicitly — REQUIRED for
  a `break`-carrying loop whose continuation needs more than the bare
  invariant: the test-false exit must then imply `P` (an `exit`-tagged
  residual) and each `break` site must establish it (with its branch facts
  `hif` in scope, which is the point).

The walk (each step is a layer-1/2 rule; nothing is proved by whole-program
execution):

* **straight-line segments** (assignments incl. tuple targets, `augAssign`,
  `pass`, expression statements, and a terminating `return`/`break`/
  `continue`) are discharged by one *captured* symbolic execution (`py_simp`'s
  lemma set at fuel 64, all local `Prop` hypotheses available as rewrites)
  spliced through `PyTriple.run_seq` or `PyTriple.of_exec`;
* **`if`** — `PyStmtTriple.ifStmt` with each branch walked under its test
  fact (`hif`); the joined midcondition is the disjunction of the branches'
  fall-through states, so the walk after the `if` forks per branch
  (`PyTriple.or_pre`); a branch whose test fact normalizes to `False` is
  closed without touching its body (`raise`-unreachability, the
  `rsa_inverse.inverse` pattern);
* **`while`** — `PyStmtTriple.whileLoop` (VC2.lean) instantiated from the
  clause pair: the invariant is
  `fun env => ∃ x₁ … xₖ tail, env = <shape> ∧ inv x₁ … xₖ` where `<shape>`
  pins unassigned slots and `tail` absorbs **environment growth** (variables
  first assigned inside the body live behind the symbolic tail via
  `Env.lookup_set_self`/`Env.lookup_set_ne`/`Env.set_set` — no hand-unrolled
  first iteration, the `rsa_inverse` pain point); the measure reads its
  variables back off the environment through `envInt`; the test-value
  function `tv` is derived by symbolic evaluation of the test at the shape
  (no Miller unification needed). Without an `exit` clause a body `break`
  weakens the loop's exit fact to the bare invariant (no negated test);
* **calls** (`x = f(…)` or `(a, b, c) = f(…)`, the call the whole right-hand
  side) — `PyStmtTriple.assign` ∘ `EvalsTo.call`, the callee fact found
  among local `CallsTo` hypotheses (recursion IHs, destructured relational
  specs) first, then the `@[py_spec]` registry; spec preconditions are
  discharged by `assumption`/`omega`, or appended as `side` goals.

Residual goals are pure mathematics over named atoms (`py_loop`
presentation: invariant conjuncts split into `hinv1`, `hinv2`, …; the loop
test as `hcont`; branch facts as `hif`; post-loop values primed), tagged
`init`, `preserve`, `dec`, `exit`, `ret`, `err`, `side`. When several
residuals share a tag (two `preserve` goals from split invariant
conjuncts), the first keeps the bare tag and the rest are numbered
(`preserve2`, `preserve3`, …) — `case preserve => …` would otherwise
silently take only the first. Anything the recipes cannot close is
*appended* as a goal, never dropped.

Entry forms: a `CallsTo` goal (`==>`/`⇓`; bridged via `PyTriple.callsTo`,
so a body that can fall off the end leaves a `v = None` residual), or a
`PyTriple` goal whose precondition reduces to `fun env => env = <literal>`
(the relational route: state `∃ v, CallsTo … v ∧ Φ v` via
`PyTriple.exists_callsTo` below, then `py_vcgen` the triple).

v1 restrictions (deliberate): loop clause variables are `Int`-valued and
must exist at loop entry; loop `orelse` is empty (the layer-2 rule's
restriction); `if`-branches are straight-line (terminators allowed; no
nested `if`/`while`/call); calls appear only as the whole right-hand side
of an assignment, with a fully literal environment (not under an enclosing
loop's symbolic tail); a loop test may not read a variable first assigned
inside the loop body; `Raises` (`==>!`) goals are not walked.
-/

namespace LeanModels.Python

/-! ## Environment-reading helpers (spec-side) -/

/-- Read an `Int`-valued variable off an environment (`0` when absent or
non-`int`) — how a loop measure derived by `py_vcgen` reads its variables
back from the interpreter environment (`μ := fun env => dec (envInt env "i") …`).
Reduces by `simp [envInt, Env.lookup]` at literal environments. -/
def envInt (env : Env) (x : String) : Int :=
  match Env.lookup env x with
  | some (.int i) => i
  | _ => 0

/-- Lookup after `Env.set` at the same key. With `Env.lookup_set_ne` and
`Env.set_set`, this is what keeps a loop-body-created variable (living
behind the invariant's symbolic environment tail) readable and writable
without the tail ever becoming literal. -/
theorem Env.lookup_set_self (e : Env) (k : String) (v : Val) :
    Env.lookup (Env.set e k v) k = some v := by
  induction e with
  | nil => simp [Env.set, Env.lookup]
  | cons kv rest ih =>
    obtain ⟨kk, kw⟩ := kv
    by_cases hk : (kk == k) = true
    · simp [Env.set, hk, Env.lookup]
    · have hk' : (kk == k) = false := by simpa using hk
      simp [Env.set, hk', Env.lookup, ih]

/-- Lookup after `Env.set` at a different key (see `Env.lookup_set_self`). -/
theorem Env.lookup_set_ne (e : Env) {k k' : String} (h : (k' == k) = false)
    (v : Val) : Env.lookup (Env.set e k v) k' = Env.lookup e k' := by
  have hne : (k == k') = false := by
    simp only [beq_eq_false_iff_ne] at h ⊢
    exact fun he => h he.symm
  induction e with
  | nil => simp [Env.set, Env.lookup, hne]
  | cons kv rest ih =>
    obtain ⟨kk, kw⟩ := kv
    by_cases hk : (kk == k) = true
    · have hkv : (kk == k') = false := by
        have : kk = k := by simpa using hk
        simpa [this] using hne
      simp [Env.set, hk, Env.lookup, hne, hkv]
    · have hk' : (kk == k) = false := by simpa using hk
      simp [Env.set, hk', Env.lookup, ih]

/-- Overwrite after `Env.set` at the same key (see `Env.lookup_set_self`). -/
theorem Env.set_set (e : Env) (k : String) (v w : Val) :
    Env.set (Env.set e k v) k w = Env.set e k w := by
  induction e with
  | nil => simp [Env.set]
  | cons kv rest ih =>
    obtain ⟨kk, kw⟩ := kv
    by_cases hk : (kk == k) = true
    · have : kk = k := by simpa using hk
      simp [Env.set, this]
    · have hk' : (kk == k) = false := by simpa using hk
      simp [Env.set, hk', ih]

/-! ## Run splicing -/

/-- Append two decided runs: statements that fell through (`.next`) followed
by any decided run of the rest — the fuel bookkeeping is internal
(`execStmt_mono`/`execStmts_mono` at a summed witness). This is the engine
of `PyTriple.run_seq`. -/
private theorem execStmts_append_run {m : Module} {l₁ l₂ : List Stmt}
    {env E' : Env} {r : Res (Env × Flow)}
    (h1 : ∃ f, execStmts m f env l₁ = .ok (E', .next))
    (h2 : ∃ f, execStmts m f E' l₂ = r) (hr : r ≠ .timeout) :
    ∃ f, execStmts m f env (l₁ ++ l₂) = r := by
  induction l₁ generalizing env with
  | nil =>
    obtain ⟨f, hf⟩ := h1
    match f, hf with
    | f + 1, hf =>
      simp only [execStmts] at hf
      have henv : env = E' := by
        have := Res.ok.inj hf
        exact congrArg Prod.fst this
      subst henv
      simpa using h2
  | cons s l₁' ih =>
    obtain ⟨f, hf⟩ := h1
    match f, hf with
    | f + 1, hf =>
      simp only [execStmts, Res.bind_eq_ok] at hf
      obtain ⟨⟨env₁, flow⟩, hstep, htail⟩ := hf
      cases flow with
      | next =>
        obtain ⟨g, hg⟩ := ih ⟨f, htail⟩
        refine ⟨f + g + 1, ?_⟩
        simp only [List.cons_append, execStmts]
        rw [execStmt_mono hstep (by simp) (f + g) (by omega)]
        simpa using execStmts_mono hg hr (f + g) (by omega)
      | ret v => simp at htail
      | brk => simp at htail
      | cont => simp at htail

/-- Splice one captured straight-line run in front of a triple for the rest:
`pre` ran to `(E', .next)` at some concrete fuel, so the triple for
`pre ++ rest` from `E` follows from the triple for `rest` from `E'`. This is
how `py_vcgen` discharges a straight-line segment before a control point. -/
theorem PyTriple.run_seq {m : Module} {E E' : Env} {f : Nat}
    {pre rest : List Stmt} {Q : PyPost}
    (h1 : execStmts m f E pre = .ok (E', .next))
    (h2 : PyTriple m (fun env => env = E') rest Q) :
    PyTriple m (fun env => env = E) (pre ++ rest) Q := by
  rintro env rfl
  obtain ⟨r, t, hr, hrun⟩ := h2.exec rfl
  obtain ⟨g, hg⟩ := execStmts_append_run ⟨f, h1⟩ ⟨t, hrun t (Nat.le_refl t)⟩
    (PyPost.holds_ne_timeout hr)
  refine ⟨g, fun F hF => ?_⟩
  rw [execStmts_mono hg (PyPost.holds_ne_timeout hr) F hF]
  exact hr

/-! ## Precondition-normalization rules

`py_vcgen` constructs preconditions in a small grammar —
`fun env => env = E`, `∃ x, P`, `P ∧ H`, `P ∨ P`, `False` — and strips them
down to the `env = E` form the walker consumes with the rules below (each
is one `apply` + `intro`). -/

universe u

/-- Strip an existential from the precondition. -/
theorem PyTriple.exists_pre {α : Sort u} {m : Module} {ss : List Stmt}
    {Q : PyPost} {P : α → Env → Prop}
    (h : ∀ x, PyTriple m (P x) ss Q) :
    PyTriple m (fun env => ∃ x, P x env) ss Q :=
  fun env hP => hP.elim fun x hx => h x env hx

/-- Hoist an existential out of a conjunction in the precondition. -/
theorem PyTriple.exists_and_pre {α : Sort u} {m : Module} {ss : List Stmt}
    {Q : PyPost} {P : α → Env → Prop} {H : Env → Prop}
    (h : ∀ x, PyTriple m (fun env => P x env ∧ H env) ss Q) :
    PyTriple m (fun env => (∃ x, P x env) ∧ H env) ss Q :=
  fun env hP => hP.1.elim fun x hx => h x env ⟨hx, hP.2⟩

/-- Reassociate a conjunction in the precondition. -/
theorem PyTriple.and_assoc_pre {m : Module} {ss : List Stmt} {Q : PyPost}
    {P H₁ H₂ : Env → Prop}
    (h : PyTriple m (fun env => P env ∧ (H₁ env ∧ H₂ env)) ss Q) :
    PyTriple m (fun env => (P env ∧ H₁ env) ∧ H₂ env) ss Q :=
  fun env hP => h env ⟨hP.1.1, hP.1.2, hP.2⟩

/-- Move the pure part of an `env = E ∧ H env` precondition into hypothesis
position (instantiated at `E`) — after this the precondition is walkable. -/
theorem PyTriple.eq_and_pre {m : Module} {ss : List Stmt} {Q : PyPost}
    {E : Env} {H : Env → Prop}
    (h : H E → PyTriple m (fun env => env = E) ss Q) :
    PyTriple m (fun env => env = E ∧ H env) ss Q :=
  fun env hP => h (hP.1 ▸ hP.2) env hP.1

/-- Split a disjunctive precondition (an `if`-join). -/
theorem PyTriple.or_pre {m : Module} {ss : List Stmt} {Q : PyPost}
    {P₁ P₂ : Env → Prop} (h1 : PyTriple m P₁ ss Q) (h2 : PyTriple m P₂ ss Q) :
    PyTriple m (fun env => P₁ env ∨ P₂ env) ss Q :=
  fun env hP => hP.elim (h1 env) (h2 env)

/-- A dead join point (both `if`-branches escaped, or an unreachable
branch: the `raise`-unreachability pattern). -/
theorem PyTriple.false_pre {m : Module} {ss : List Stmt} {Q : PyPost} :
    PyTriple m (fun _ => False) ss Q :=
  fun _ hP => hP.elim

/-! ## The relational bridge

`PyTriple.callsTo` (VC2.lean) requires the returned value fixed up front;
relational specs (`extended_gcd`'s Bezout coefficients) only know it
*exists*. This bridge closes the gap: prove the whole-body triple with an
arbitrary predicate `Φ` on the returned value (a `PyTriple` goal `py_vcgen`
walks directly), get `∃ v, CallsTo … v ∧ Φ v`. -/

/-- Triple → arrow, relational form: a whole-body triple whose `ret` arm
asserts `Φ` of the returned value (and whose `next` arm is `False` — the
body always returns) yields an existential `CallsTo`. -/
theorem PyTriple.exists_callsTo {m : Module} {fname : String}
    {f : FunctionDefn} {args : Array Val} {Φ : Val → Prop}
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : args.size = f.params.size)
    (h : PyTriple m (fun env => env = mkCallEnv f.params args) f.body.toList
        { next := fun _ => False, ret := fun w _ => Φ w }) :
    ∃ v, CallsTo m fname args v ∧ Φ v := by
  obtain ⟨r, t, hr, hrun⟩ := h.exec rfl
  have hrt := hrun t (Nat.le_refl t)
  cases r with
  | ok p =>
    obtain ⟨env', flow⟩ := p
    cases flow with
    | next => exact hr.elim
    | ret w =>
      refine ⟨w, ⟨t + 1, ?_⟩, hr⟩
      rw [callFunction, hf]
      simp [hargsOk, hlocalsOk, harity, hrt]
    | brk => exact hr.elim
    | cont => exact hr.elim
  | exn e => exact hr.elim
  | timeout => exact (PyPost.holds_ne_timeout hr rfl).elim
  | unsupported msg => exact hr.elim

/-! ## The walker (meta level) -/

namespace PyVCGen

open Lean Elab Tactic Meta PyLoopTactic

/-- Fuel for every captured symbolic run (a depth bound, so a generous
constant covers everything straight-line). -/
def fuelK : Nat := 64

/-- Interpreter definitions unfolded during captured symbolic execution
(the `py_simp` list plus `envInt`). -/
def interpUnfolds : List Name :=
  [``execStmts, ``execStmt, ``evalExpr, ``evalExprs, ``evalBoolChain,
   ``evalCompareChain, ``findFunction, ``mkCallEnv, ``Env.lookup, ``Env.set,
   ``Const.toVal, ``truthy, ``asInt, ``valEq, ``valEqList, ``intCmp,
   ``strCmp, ``evalCompareOp, ``evalBinOp, ``evalUnaryOp, ``lenVal,
   ``normIndex, ``indexVal, ``targetNames, ``bindAll, ``assignTo, ``envInt]

/-- Rewrite lemmas added to captured symbolic execution: the branch-collapse
of loop tests and the symbolic-tail environment lemmas. -/
def interpLemmas : List Name :=
  [``ite_ok_bool, ``Env.lookup_set_self, ``Env.lookup_set_ne, ``Env.set_set]

/-- The truthiness-normalization set: turns `truthy <captured value> = true`
facts into the clean arithmetic propositions residual goals should show. -/
def normLemmas : List Name :=
  [``decide_eq_true_eq, ``decide_eq_false_iff_not, ``Bool.not_eq_true',
   ``Bool.not_eq_false', ``Bool.not_eq_eq_eq_not, ``Bool.not_true,
   ``Bool.not_false, ``beq_iff_eq, ``beq_eq_false_iff_ne, ``bne_iff_ne,
   ``Decidable.not_not]

/-- Definitions unfolded by the normalization set. -/
def normUnfolds : List Name := [``truthy, ``envInt, ``Env.lookup]

/-- Presentation lemmas for residual goals (marshalling peeled, `Val`
injectivity applied). -/
def presentLemmas : List Name :=
  [``toVal_int, ``toVal_nat, ``toVal_bool, ``toVal_str, ``toVal_val,
   ``toVal_list, ``toVal_int_triple, ``Val.int.injEq, ``Val.bool.injEq,
   ``Val.str.injEq, ``Val.tuple.injEq, ``Val.list.injEq]

/-- The three simp contexts of a `py_vcgen` run: `exec` (symbolic
execution: default set + interpreter unfolds + program literal), `norm`
(truthiness normalization only), `present` (residual-goal cleanup). -/
structure SimpPack where
  exec : Simp.Context
  norm : Simp.Context
  present : Simp.Context
  procs : Simp.SimprocsArray

private def addAll (thms : SimpTheorems) (unfolds lemmas : List Name) :
    MetaM SimpTheorems := do
  let mut thms := thms
  for n in unfolds do
    thms ← thms.addDeclToUnfold n
  for n in lemmas do
    thms ← thms.addConst n
  return thms

/-- Build the simp contexts, `progs` the program constants to unfold. -/
def mkPack (progs : List Name) : MetaM SimpPack := do
  let congr ← getSimpCongrTheorems
  let execThms ← addAll (← getSimpTheorems)
    (interpUnfolds ++ progs) interpLemmas
  let normThms ← addAll (← getSimpTheorems) normUnfolds
    (normLemmas ++ interpLemmas)
  let presentThms ← addAll (← getSimpTheorems) (normUnfolds ++ progs)
    (normLemmas ++ presentLemmas ++ interpLemmas)
  return {
    exec := ← Simp.mkContext {} #[execThms] congr
    norm := ← Simp.mkContext {} #[normThms] congr
    present := ← Simp.mkContext {} #[presentThms] congr
    procs := #[← Simp.getSimprocs] }

/-- All accessible `Prop`-typed hypotheses of the current local context —
supplied to every captured run as rewrite rules (this is how a loop-test
fact `hcont : b ≠ 0` decides the `ZeroDivisionError` guard of `%`, and a
branch fact `hif` decides a nested test). -/
def currentFacts : MetaM (Array FVarId) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if (← isProp d.type) then
      out := out.push d.fvarId
  return out

/-- Extend a simp context with hypothesis facts. -/
def addFacts (ctx : Simp.Context) (facts : Array FVarId) :
    MetaM Simp.Context := do
  let mut thms := ctx.simpTheorems
  for fv in facts do
    try
      thms ← thms.addTheorem (.fvar fv) (mkFVar fv)
    catch _ => pure ()
  return ctx.setSimpTheorems thms

/-- Symbolically execute `e` (an interpreter term) with the local `Prop`
hypotheses as extra rewrites; returns the normal form and a proof `e = nf`. -/
def captureRun (pack : SimpPack) (e : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let ctx ← addFacts pack.exec (← currentFacts)
  let (r, _) ← Meta.simp e ctx pack.procs
  let prf ← match r.proof? with
    | some p =>
      -- Pin the equation's syntactic form: simp folds definitional steps
      -- away, so the proof's inferred type may show an unfolded lhs.
      mkExpectedTypeHint p (← mkEq e r.expr)
    | none => mkEqRefl e
  return (r.expr, prf)

/-- Apply a constant to optional arguments, filling `none` positions (and
missing trailing hypotheses) with fresh metavariables — the `apply`-ready
partial-application builder (`mkAppOptM` refuses unassigned mvars). -/
def appOpt (n : Name) (args : Array (Option Lean.Expr)) : MetaM Lean.Expr := do
  let f ← mkConstWithFreshMVarLevels n
  let mut e := f
  let mut ty ← inferType f
  for a in args do
    ty ← whnf ty
    let .forallE _ d b _ := ty
      | throwError "py_vcgen: internal — too many arguments for {n}"
    match a with
    | some x =>
      unless ← isDefEq d (← inferType x) do
        throwError "py_vcgen: internal — argument type mismatch for {n}: expected{indentExpr d}\ngot{indentExpr (← inferType x)}"
      e := mkApp e x
      ty := b.instantiate1 x
    | none =>
      let mv ← mkFreshExprMVar d
      e := mkApp e mv
      ty := b.instantiate1 mv
  return e

/-- Normalize a proposition with the truthiness set; returns the normal form
and (when changed) a proof `p = p'`. -/
def normProp (pack : SimpPack) (p : Lean.Expr) :
    MetaM (Lean.Expr × Option Lean.Expr) := do
  let (r, _) ← Meta.simp p pack.norm pack.procs
  return (r.expr, r.proof?)

/-! ### Literal introspection -/

/-- `Array α` literal → its `List` literal. -/
def arrToList (a : Lean.Expr) : MetaM Lean.Expr := do
  let a ← whnfR a
  if a.isAppOfArity ``Array.mk 2 then return a.getArg! 1
  else if a.isAppOfArity ``List.toArray 2 then return a.getArg! 1
  else throwError "py_vcgen: expected a literal array:{indentExpr a}"

/-- Split a `List` literal into its element expressions and its terminator
(the trailing `List.nil` or any non-`cons` tail); sees through
`Array.toList` of literal arrays. -/
partial def parseListLit (e : Lean.Expr) : MetaM (Array Lean.Expr × Lean.Expr) := do
  let e ← whnfR e
  if e.isAppOfArity ``List.cons 3 then
    let (rest, tail) ← parseListLit (e.getArg! 2)
    return (#[e.getArg! 1] ++ rest, tail)
  else if e.isAppOfArity ``Array.toList 2 then
    parseListLit (← arrToList (e.getArg! 1))
  else
    return (#[], e)

/-- Is this expression the `List.nil` terminator? -/
def isNilTail (e : Lean.Expr) : Bool := e.isAppOfArity ``List.nil 1

/-- Rebuild a `List` literal from elements and a tail expression. -/
def mkListLit' (ty : Lean.Expr) (elems : Array Lean.Expr) (tail : Lean.Expr) :
    Lean.Expr :=
  elems.foldr (fun e acc =>
    mkApp3 (Lean.mkConst ``List.cons [Level.zero]) ty e acc) tail

/-- The `String × Val` pair type of environment entries. -/
def entryTy : Lean.Expr :=
  mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) (Lean.mkConst ``String)
    (Lean.mkConst ``Val)

/-- The `List (String × Val)` environment type. -/
def envTy : Lean.Expr := mkApp (Lean.mkConst ``List [Level.zero]) entryTy

/-- An environment shape: named literal cons-entries, then a spine of
`Env.set` writes (outermost first — variables that grew into the symbolic
region), over a symbolic tail. The `sets` region is where loop-body-created
variables live (`Env.set (… tl …) "q" v`), readable/writable through
`Env.lookup_set_self`/`Env.set_set` without the tail ever becoming
literal. -/
structure EnvShape where
  entries : Array (String × Lean.Expr)
  sets : Array (String × Lean.Expr) := #[]
  tail : Lean.Expr

/-- Parse an environment expression into its literal cons-prefix, its
`Env.set` tail spine, and its symbolic tail. -/
def parseEnvShape (e : Lean.Expr) : MetaM EnvShape := do
  let (elems, tail) ← parseListLit e
  let mut entries := #[]
  for el in elems do
    let el ← whnfR el
    unless el.isAppOfArity ``Prod.mk 4 do
      throwError "py_vcgen: environment entry is not a literal pair:{indentExpr el}"
    let nameE ← whnfR (el.getArg! 2)
    let .lit (.strVal name) := nameE
      | throwError "py_vcgen: environment name is not a string literal:{indentExpr nameE}"
    entries := entries.push (name, el.getArg! 3)
  let mut sets := #[]
  let mut base ← whnfR tail
  for _ in [0:64] do
    if base.isAppOfArity ``Env.set 3 then
      let .lit (.strVal k) ← whnfR (base.getArg! 1)
        | throwError "py_vcgen: `Env.set` key is not a string literal:{indentExpr base}"
      sets := sets.push (k, base.getArg! 2)
      base ← whnfR (base.getArg! 0)
    else
      break
  return { entries, sets, tail := base }

/-- Rebuild an environment expression from a shape. -/
def mkEnvExpr (sh : EnvShape) : Lean.Expr :=
  let tail := sh.sets.foldr (init := sh.tail) fun (k, v) acc =>
    mkApp3 (Lean.mkConst ``Env.set) acc (mkStrLit k) v
  mkListLit' entryTy
    (sh.entries.map fun (n, v) =>
      mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero])
        (Lean.mkConst ``String) (Lean.mkConst ``Val) (mkStrLit n) v)
    tail

/-- The names assigned (as `Name`/`Tuple`/`List` targets or `augAssign`
targets) anywhere in a statement, recursively through `if`/`while`. -/
partial def stmtAssignedNames (s : Lean.Expr) : MetaM (Array String) := do
  let s ← whnfR s
  let fn := s.getAppFn
  let .const c _ := fn | return #[]
  let fromTarget (t : Lean.Expr) : MetaM (Array String) := do
    let t ← whnfR t
    if t.isAppOfArity ``Expr.name 2 then
      let .lit (.strVal n) ← whnfR (t.getArg! 0) | return #[]
      return #[n]
    else if t.isAppOfArity ``Expr.tuple 2 || t.isAppOfArity ``Expr.list 2 then
      let (elems, _) ← parseListLit (← arrToList (t.getArg! 0))
      let mut out := #[]
      for el in elems do
        let el ← whnfR el
        if el.isAppOfArity ``Expr.name 2 then
          if let .lit (.strVal n) := ← whnfR (el.getArg! 0) then
            out := out.push n
      return out
    else return #[]
  match c with
  | ``Stmt.assign => do
    let (tgts, _) ← parseListLit (← arrToList (s.getArg! 0))
    let mut out := #[]
    for t in tgts do out := out ++ (← fromTarget t)
    return out
  | ``Stmt.augAssign => fromTarget (s.getArg! 0)
  | ``Stmt.ifStmt | ``Stmt.whileLoop => do
    let (b1, _) ← parseListLit (← arrToList (s.getArg! 1))
    let (b2, _) ← parseListLit (← arrToList (s.getArg! 2))
    let mut out := #[]
    for t in b1 ++ b2 do out := out ++ (← stmtAssignedNames t)
    return out
  | _ => return #[]

/-- Does the statement contain a `break` at its own loop level (recursing
into `if`s but not into nested loops)? -/
partial def stmtHasBreak (s : Lean.Expr) : MetaM Bool := do
  let s ← whnfR s
  let .const c _ := s.getAppFn | return false
  match c with
  | ``Stmt.brk => return true
  | ``Stmt.ifStmt => do
    let (b1, _) ← parseListLit (← arrToList (s.getArg! 1))
    let (b2, _) ← parseListLit (← arrToList (s.getArg! 2))
    (b1 ++ b2).anyM stmtHasBreak
  | _ => return false

/-- All `while` statements in a statement list, in source order (recursing
through `if` branches and loop bodies) — the loop⇄clause index, robust
across `if`-forks re-walking the same loop. -/
partial def collectLoops (ss : Array Lean.Expr) : MetaM (Array Lean.Expr) := do
  let mut out := #[]
  for s in ss do
    let s ← whnfR s
    let .const c _ := s.getAppFn | continue
    match c with
    | ``Stmt.whileLoop =>
      out := out.push s
      let (b, _) ← parseListLit (← arrToList (s.getArg! 1))
      out := out ++ (← collectLoops b)
    | ``Stmt.ifStmt =>
      let (b1, _) ← parseListLit (← arrToList (s.getArg! 1))
      let (b2, _) ← parseListLit (← arrToList (s.getArg! 2))
      out := out ++ (← collectLoops b1) ++ (← collectLoops b2)
    | _ => continue
  return out

/-! ### PyPost plumbing -/

/-- The five arms of a `PyPost` expression (direct constructor arguments
when literal, projection applications otherwise). -/
def getPostArms (q : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := do
  let q' ← whnfR q
  if q'.isAppOfArity ``PyPost.mk 5 then
    -- whnfR each field: nested `{Q with next := R}` posts store the
    -- untouched arms as projection applications of the inner literal.
    return (← whnfR (q'.getArg! 0), ← whnfR (q'.getArg! 1),
            ← whnfR (q'.getArg! 2), ← whnfR (q'.getArg! 3),
            ← whnfR (q'.getArg! 4))
  else
    return (← mkAppM ``PyPost.next #[q], ← mkAppM ``PyPost.ret #[q],
            ← mkAppM ``PyPost.brk #[q], ← mkAppM ``PyPost.cont #[q],
            ← mkAppM ``PyPost.err #[q])

/-! ### Residual bookkeeping -/

/-- Per-arm residual tag: the case name, and whether the arm is the loop
body's `Inv ∧ μ < n` conjunction (split into `preserve` + `dec` goals). -/
structure ArmTag where
  tag : Name
  split2 : Bool := false

/-- Residual tags for the five arms of the current postcondition. -/
structure PostTags where
  next : ArmTag
  ret : ArmTag
  brk : ArmTag
  cont : ArmTag
  err : ArmTag

/-- The walker's state and configuration. -/
structure VCCtx where
  pack : SimpPack
  mE : Lean.Expr
  clauses : Array (Term × Term)
  /-- Optional per-loop exit clauses, keyed by 0-based loop index. -/
  exits : Array (Nat × Term)
  loops : Array Lean.Expr
  residuals : IO.Ref (Array MVarId)
  clauseGoals : IO.Ref (Array MVarId)
  delayed : IO.Ref (Array (Nat × Lean.Expr × Lean.Expr))
  /-- Delayed exit-clause metavariables (loop index ↦ mvar): in delayed mode
  a `break`-carrying loop gets its exit clause requested as a goal
  (`exit<i>`), mirroring `inv<i>`/`dec<i>`. -/
  delayedExits : IO.Ref (Array (Nat × Lean.Expr))

/-- `MVarId.apply`, dropping the delayed inv/dec clause metavariables from
the returned goals (they are tracked separately and would otherwise leak
back out of every application whose term mentions them). -/
def applyC (ctx : VCCtx) (g : MVarId) (e : Lean.Expr) : MetaM (List MVarId) := do
  let gs ← g.apply e
  let cg ← ctx.clauseGoals.get
  return gs.filter (fun g' => !cg.contains g')

/-- Scrub plumbing hypotheses out of an `exit`-tagged residual: the
symbolic environment tail `tl` (and any shadowed copies) is presentation
noise once the shape solving is done — clear every clearable hypothesis so
named; `env`/`heqE` no longer arise (`destructInvHyp` substitutes them
away). A `tl` the goal still mentions (an environment-growth exit fact
quantifying over the tail, `nested_flow`'s inner loop) survives — it is
content there, not noise. -/
def scrubExitNoise (g : MVarId) : MetaM MVarId := do
  let fvs ← g.withContext do
    let mut fvs : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if [`tl, `env, `heqE].contains d.userName.eraseMacroScopes then
        fvs := fvs.push d.fvarId
    pure fvs
  g.tryClearMany fvs

/-- Present a residual goal: cleanup simp, `assumption` attempt, tag, push.
Never drops a goal it cannot close. -/
def addResidual (ctx : VCCtx) (g : MVarId) (tag : Name) : MetaM Unit := do
  let r ← try
      Prod.fst <$> Meta.simpGoal g ctx.pack.present ctx.pack.procs
    catch _ => pure (some (#[], g))   -- no-progress simp: present as-is
  match r with
  | none => return
  | some (_, g) =>
    match ← g.withContext (do
        match ← findLocalDeclWithType? (← g.getType) with
        | some fv => g.assign (mkFVar fv); pure true
        | none => pure false) with
    | true => return
    | false =>
      let g ← if tag == `exit then scrubExitNoise g else pure g
      g.setTag tag
      ctx.residuals.modify (·.push g)

/-! ### The conjunction/witness solver -/

/-- Solve a postcondition-arm shape (`∃`-nests over an environment
equation, conjunctions, `if`-join disjunctions): equations with unification
variables must close by `isDefEq` (they pin the witnesses); ground leaves
close by `rfl`-unification or `assumption`, and otherwise become residual
metavariable goals (returned with the proof). In `strict` mode no residuals
are allowed (used to pick an `if`-join disjunct). -/
partial def solveShape (ctx : VCCtx) (ty : Lean.Expr) (strict : Bool) :
    MetaM (Option (Lean.Expr × Array MVarId)) := do
  let ty := (← instantiateMVars ty).headBeta
  if ty.isAppOfArity ``And 2 then
    let some (p1, r1) ← solveShape ctx (ty.getArg! 0) strict | return none
    let some (p2, r2) ← solveShape ctx (ty.getArg! 1) strict | return none
    return some (mkApp4 (Lean.mkConst ``And.intro) (ty.getArg! 0)
      (ty.getArg! 1) p1 p2, r1 ++ r2)
  else if ty.isAppOfArity ``Or 2 then
    let a := ty.getArg! 0
    let b := ty.getArg! 1
    let attempt (side : Lean.Expr) (isLeft : Bool) (st : Bool) :
        MetaM (Option (Lean.Expr × Array MVarId)) := do
      let s ← saveState
      match ← solveShape ctx side st with
      | some (p, rs) =>
        let intro := if isLeft then ``Or.inl else ``Or.inr
        return some (mkApp3 (Lean.mkConst intro) a b p, rs)
      | none => restoreState s; return none
    if let some r ← attempt a true true then return some r
    if let some r ← attempt b false true then return some r
    if strict then return none
    if let some r ← attempt a true false then return some r
    if let some r ← attempt b false false then return some r
    return none
  else if ty.isAppOfArity ``Exists 2 then
    let α := ty.getArg! 0
    let p := ty.getArg! 1
    let w ← mkFreshExprMVar α
    let some (inner, rs) ← solveShape ctx (p.beta #[w]) strict | return none
    unless (← instantiateMVars w).findMVar? (fun _ => true) |>.isNone do
      return none
    let u ← getLevel α
    return some (mkApp4 (Lean.mkConst ``Exists.intro [u]) α p
      (← instantiateMVars w) inner, rs)
  else if ty.isAppOfArity ``Eq 3 then
    let lhs := ty.getArg! 1
    let rhs := ty.getArg! 2
    let hasMVar := (← instantiateMVars ty).hasExprMVar
    let s ← saveState
    if ← withReducible (isDefEq lhs rhs) then
      return some (← mkEqRefl (← instantiateMVars lhs), #[])
    restoreState s
    if ← isDefEq lhs rhs then
      return some (← mkEqRefl (← instantiateMVars lhs), #[])
    restoreState s
    match ← findLocalDeclWithType? (← instantiateMVars ty) with
    | some fv => return some (mkFVar fv, #[])
    | none =>
    if hasMVar then return none
    if strict then return none
    let g ← mkFreshExprMVar ty .syntheticOpaque
    return some (g, #[g.mvarId!])
  else if ty.isConstOf ``True then
    return some (Lean.mkConst ``True.intro, #[])
  else if ty.isConstOf ``False then
    if strict then return none
    let g ← mkFreshExprMVar ty .syntheticOpaque
    return some (g, #[g.mvarId!])
  else
    match ← findLocalDeclWithType? (← instantiateMVars ty) with
    | some fv => return some (mkFVar fv, #[])
    | none =>
      if strict then return none
      if (← instantiateMVars ty).hasExprMVar && !ty.getAppFn.isMVar then
        return none
      let g ← mkFreshExprMVar ty .syntheticOpaque
      return some (g, #[g.mvarId!])

/-- Close a goal through `solveShape`, pushing the leaves as residuals
tagged `tag`; falls back to presenting the whole goal. -/
def closeByShape (ctx : VCCtx) (g : MVarId) (tag : Name) : MetaM Unit := do
  g.withContext do
    let ty ← Core.betaReduce (← instantiateMVars (← g.getType))
    match ← solveShape ctx ty false with
    | some (prf, residuals) =>
      g.assign prf
      for r in residuals do
        addResidual ctx r tag
    | none =>
      addResidual ctx g tag

/-- Close an arm goal per its tag: a loop-body `next`/`cont` arm
(`Inv ∧ μ < n`) is split into a `preserve` part and a `dec` part. -/
def closeArm (ctx : VCCtx) (g : MVarId) (at_ : ArmTag) : MetaM Unit := do
  g.withContext do
    let ty ← Core.betaReduce (← instantiateMVars (← g.getType))
    if at_.split2 && ty.isAppOfArity ``And 2 then
      let gL ← mkFreshExprMVar (ty.getArg! 0) .syntheticOpaque
      let gR ← mkFreshExprMVar (ty.getArg! 1) .syntheticOpaque
      g.assign (mkApp4 (Lean.mkConst ``And.intro) (ty.getArg! 0)
        (ty.getArg! 1) gL gR)
      closeByShape ctx gL.mvarId! at_.tag
      closeByShape ctx gR.mvarId! `dec
    else
      closeByShape ctx g at_.tag

/-! ### Goal parsing -/

/-- Statement classification for the walk. -/
inductive StmtKind where
  | plain | term | ctrlWhile | ctrlIf | ctrlCall
deriving BEq, Inhabited

/-- Classify one statement: control (`while`/`if`/call-assignment),
terminator (`return`/`break`/`continue`), or plain straight-line. -/
def classify (s : Lean.Expr) : MetaM StmtKind := do
  let s ← whnfR s
  let .const c _ := s.getAppFn | return .plain
  match c with
  | ``Stmt.whileLoop => return .ctrlWhile
  | ``Stmt.ifStmt => return .ctrlIf
  | ``Stmt.ret | ``Stmt.brk | ``Stmt.cont => return .term
  | ``Stmt.assign => do
    let rhs ← whnfR (s.getArg! 1)
    if rhs.isAppOfArity ``Expr.call 4 then
      let fn ← whnfR (rhs.getArg! 0)
      let unsup ← whnfR (rhs.getArg! 2)
      if fn.isAppOfArity ``Expr.name 2 && unsup.isAppOfArity ``Option.none 1 then
        return .ctrlCall
    return .plain
  | _ => return .plain

/-- The `Stmt` type constant. -/
def stmtTy : Lean.Expr := Lean.mkConst ``Stmt
/-- `List.nil` at `Stmt`. -/
def nilStmts : Lean.Expr :=
  mkApp (Lean.mkConst ``List.nil [Level.zero]) stmtTy
/-- Rebuild a literal `List Stmt`. -/
def mkStmtsLit (ss : Array Lean.Expr) : Lean.Expr := mkListLit' stmtTy ss nilStmts

/-- A parsed and normalized `PyTriple` goal: precondition
`fun env => env = E` with `E` in literal shape, statement list literal. -/
structure TripleGoal where
  g : MVarId
  m : Lean.Expr
  E : Lean.Expr
  shape : EnvShape
  stmts : Array Lean.Expr
  Q : Lean.Expr

/-- Extract `E` from a `fun env => env = E` precondition. -/
def envOfPred (P : Lean.Expr) : MetaM Lean.Expr := do
  let P ← instantiateMVars P
  match P with
  | .lam _ _ body _ =>
    if body.isAppOfArity ``Eq 3 && body.getArg! 1 == .bvar 0 &&
        !(body.getArg! 2).hasLooseBVars then
      return body.getArg! 2
    else
      throwError "py_vcgen: precondition is not `fun env => env = E`:{indentExpr P}"
  | _ => throwError "py_vcgen: precondition is not a lambda:{indentExpr P}"

/-- The environment-equality precondition `fun env => env = E`. -/
def mkEqPred (E : Lean.Expr) : MetaM Lean.Expr :=
  withLocalDeclD `env envTy fun env =>
    mkLambdaFVars #[env] (mkApp3 (Lean.mkConst ``Eq [.succ .zero]) envTy env E)

/-- Split the goals of a `consequence` application into
`(h, hpre, hpost)`. -/
def splitConsGoals (gs : List MVarId) : MetaM (MVarId × MVarId × MVarId) := do
  let mut h : Option MVarId := none
  let mut hpre : Option MVarId := none
  let mut hpost : Option MVarId := none
  for g in gs do
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``PyTriple || t.isAppOf ``PyStmtTriple then h := some g
    else if t.isAppOf ``PyPost.Entails then hpost := some g
    else hpre := some g
  let (some a, some b, some c) := (h, hpre, hpost)
    | throwError "py_vcgen: internal — consequence goals"
  return (a, b, c)

/-- Split the goals of a `PyTriple.seq` application into `(h1, h2)`. -/
def splitSeqGoals (gs : List MVarId) : MetaM (MVarId × MVarId) := do
  let mut h1 : Option MVarId := none
  let mut h2 : Option MVarId := none
  for g in gs do
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``PyStmtTriple then h1 := some g
    else if t.isAppOf ``PyTriple then h2 := some g
  let (some a, some b) := (h1, h2)
    | throwError "py_vcgen: internal — seq goals"
  return (a, b)

/-- Parse a `PyTriple` goal into its parts, normalizing the precondition to
`fun env => env = <literal shape>` (through captured reduction +
`consequence` when needed) and the statement list to a literal. -/
partial def parseTripleGoal (ctx : VCCtx) (g : MVarId) : MetaM TripleGoal := do
  g.withContext do
    let tgtOrig ← instantiateMVars (← g.getType)
    let tgt ← Core.betaReduce tgtOrig
    unless tgt.isAppOfArity ``PyTriple 4 do
      throwError "py_vcgen: expected a PyTriple goal:{indentExpr tgt}"
    -- Inspect through the beta-reduced form, but rebuild with the ORIGINAL
    -- components: beta-variant types containing the delayed clause mvars are
    -- not decidable by `isDefEq` (opaque flex applications), identical ones
    -- are.
    let m := tgtOrig.getArg! 0
    let P := tgtOrig.getArg! 1
    let ssE := tgtOrig.getArg! 2
    let Q := tgtOrig.getArg! 3
    let E ← envOfPred (tgt.getArg! 1)
    let sh? ← try some <$> parseEnvShape E catch _ => pure none
    -- A shape whose tail base is neither `[]` nor a variable (e.g. a raw
    -- `mkCallEnv …` entry environment) must be reduced first.
    let sh? := match sh? with
      | some sh => if isNilTail sh.tail || sh.tail.isFVar then some sh else none
      | none => none
    match sh? with
    | some sh =>
      let (stmts, tail) ← parseListLit ssE
      unless isNilTail tail do
        throwError "py_vcgen: statement list is not literal:{indentExpr ssE}"
      let ssLit := mkStmtsLit stmts
      let g ← g.change (mkApp4 (Lean.mkConst ``PyTriple) m P ssLit Q)
      return { g, m, E, shape := sh, stmts, Q }
    | none =>
      let (E', prfE) ← captureRun ctx.pack E
      let _ ← parseEnvShape E'   -- throw early if still unusable
      let P' ← mkEqPred E'
      let consT ← appOpt ``PyTriple.consequence
        #[some m, some P', some P, some ssE, some Q, some Q, none, none, none]
      let gs ← applyC ctx g consT
      let (h, hpre, hpost) ← splitConsGoals gs
      hpost.withContext do
        let _ ← applyC ctx hpost (← mkAppM ``PyPost.Entails.rfl #[Q])
      let (_, gp) ← hpre.intro `env
      let (heqFv, gp) ← gp.intro `henv
      gp.withContext do
        let _ ← applyC ctx gp (← mkAppM ``Eq.trans #[mkFVar heqFv, prfE])
      parseTripleGoal ctx h

/-! ### Captured-run parsing -/

/-- The decided outcome of a captured run. -/
inductive RunOut where
  | next (env : Lean.Expr)
  | ret (v env : Lean.Expr)
  | brk (env : Lean.Expr)
  | cont (env : Lean.Expr)
  | exn (e : Lean.Expr)

/-- Parse a captured `Res (Env × Flow)` normal form. -/
def parseRun (r : Lean.Expr) : MetaM (Option RunOut) := do
  let r ← whnfR r
  if r.isAppOfArity ``Res.ok 2 then
    let p ← whnfR (r.getArg! 1)
    unless p.isAppOfArity ``Prod.mk 4 do return none
    let env := p.getArg! 2
    let flow ← whnfR (p.getArg! 3)
    if flow.isConstOf ``Flow.next then return some (.next env)
    else if flow.isAppOfArity ``Flow.ret 1 then
      return some (.ret (flow.getArg! 0) env)
    else if flow.isConstOf ``Flow.brk then return some (.brk env)
    else if flow.isConstOf ``Flow.cont then return some (.cont env)
    else return none
  else if r.isAppOfArity ``Res.exn 2 then
    return some (.exn (r.getArg! 1))
  else return none

/-- Close the arm goal of a decided run against the postcondition:
`Eq.mpr (congrArg Q.holds prf)` reduces `Q.holds r` to the arm
definitionally; the arm becomes a shaped/residual goal. -/
def closeRun (ctx : VCCtx) (tags : PostTags) (g : MVarId) (Q r prf : Lean.Expr) :
    MetaM Unit := do
  g.withContext do
    let some out ← parseRun r
      | throwError "py_vcgen: symbolic execution got stuck (out-of-tier statement, or a hypothesis is missing):{indentExpr r}"
    let (nx, rt, bk, ct, er) ← getPostArms Q
    let (armTy, at_) := match out with
      | .next env => (mkApp nx env, tags.next)
      | .ret v env => (mkApp2 rt v env, tags.ret)
      | .brk env => (mkApp bk env, tags.brk)
      | .cont env => (mkApp ct env, tags.cont)
      | .exn e => (mkApp er e, tags.err)
    let armTy := armTy.headBeta
    let gArm ← mkFreshExprMVar armTy .syntheticOpaque
    let holdsFn := mkApp (Lean.mkConst ``PyPost.holds) Q
    let heq ← mkCongrArg holdsFn prf
    g.assign (← mkAppM ``Eq.mpr #[heq, gArm])
    closeArm ctx gArm.mvarId! at_

/-! ### Small dischargers -/

/-- Close an equation side goal whose two sides are definitionally equal
(literal-module guards: `argsOk`, arity, …). -/
def closeRfl (g : MVarId) : MetaM Unit := do
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let some (_, lhs, _) := t.eq?
      | throwError "py_vcgen: expected an equation side goal:{indentExpr t}"
    let closed ← try
        let gs ← g.apply (← mkEqRefl lhs)
        pure gs.isEmpty
      catch _ => pure false
    unless closed do
      throwError "py_vcgen: side condition did not close by rfl (out-of-tier function, arity mismatch?):{indentExpr t}"

/-- Run a tactic on a detached goal; `true` iff it closed the goal
(state restored otherwise). -/
def tryTacClose (g : MVarId) (tac : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  try
    let gs ← Lean.Elab.Tactic.run g (evalTactic tac)
    if gs.isEmpty then return true
    s.restore
    return false
  catch _ =>
    s.restore
    return false

/-- Discharge a callee-spec side condition: `assumption`, then `omega`,
else a residual tagged `side`. -/
def trySide (ctx : VCCtx) (g : MVarId) : TacticM Unit := do
  if ← g.isAssigned then return
  let closed ← g.withContext do
    match ← findLocalDeclWithType? (← instantiateMVars (← g.getType)) with
    | some fv => g.assign (mkFVar fv); pure true
    | none => pure false
  if closed then return
  if ← tryTacClose g (← `(tactic| omega)) then return
  addResidual ctx g `side

/-! ### Callee-spec lookup -/

/-- Find a `CallsTo` fact for `fname` at the evaluated argument values:
local hypotheses first (recursion IHs, destructured relational facts), then
the `@[py_spec]` registry. Returns the fact, the result value, and any
uninstantiated spec preconditions as side goals. -/
def findCalleeFact (ctx : VCCtx) (fname : String) (vsLit : Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr × Array MVarId)) := do
  let vsArr ← mkAppM ``List.toArray #[vsLit]
  let mkTarget : MetaM (Lean.Expr × Lean.Expr) := do
    let v ← mkFreshExprMVar (Lean.mkConst ``Val)
    return (mkApp4 (Lean.mkConst ``CallsTo) ctx.mE (mkStrLit fname) vsArr v, v)
  -- local hypotheses, most recent first
  for d in (← getLCtx).decls.toList.filterMap id |>.reverse do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``CallsTo 4 then
      let s ← saveState
      let (target, v) ← mkTarget
      if ← isDefEq t target then
        return some (d.toExpr, ← instantiateMVars v, #[])
      s.restore
  -- the @[py_spec] registry
  for n in ← Lean.labelled `py_spec do
    let s ← saveState
    let res? ← try
        let lemE ← mkConstWithFreshMVarLevels n
        let (ms, _, concl) ← forallMetaTelescope (← inferType lemE)
        let concl ← whnfR concl
        if concl.isAppOfArity ``CallsTo 4 then
          let (target, v) ← mkTarget
          if ← isDefEq concl target then
            let mut sides : Array MVarId := #[]
            let mut ok := true
            for mv in ms do
              let mvId := mv.mvarId!
              if ← mvId.isAssigned then continue
              if ← isProp (← inferType mv) then
                sides := sides.push mvId
              else
                ok := false
            if ok then
              pure (some (mkAppN lemE ms, ← instantiateMVars v, sides))
            else pure none
          else pure none
        else pure none
      catch _ => pure none
    match res? with
    | some r => return some r
    | none => s.restore
  return none

/-! ### Loop-artifact construction helpers -/

/-- `∃ x₁ …, body`, abstracting the given fvars in order. -/
def mkExistsNest (fvs : Array Lean.Expr) (body : Lean.Expr) :
    MetaM Lean.Expr := do
  let mut b := body
  for fv in fvs.reverse do
    let lam ← mkLambdaFVars #[fv] b
    b ← mkAppM ``Exists #[lam]
  return b

/-- Strip an `∃`/`∧` precondition down to `fun env => env = E`, introducing
existential witnesses with `introNames` (in order) and the pure part as a
hypothesis named `hypName`. Applies the precondition-normalization rules
(`exists_pre`/`exists_and_pre`/`and_assoc_pre`/`eq_and_pre`). -/
def normalizePre (ctx : VCCtx) (introNames : Array Name) (hypName : Name)
    (g : MVarId) : MetaM MVarId := do
  let mut g := g
  let mut ni := 0
  for _ in [0:64] do
    let tgt ← g.withContext do
      Core.betaReduce (← instantiateMVars (← g.getType))
    unless tgt.isAppOfArity ``PyTriple 4 do
      throwError "py_vcgen: internal — normalizePre on a non-triple:{indentExpr tgt}"
    let .lam _ _ body _ := tgt.getArg! 1
      | throwError "py_vcgen: internal — precondition is not a lambda"
    if body.isAppOfArity ``Eq 3 then
      return g
    else if body.isAppOfArity ``Exists 2 then
      let [g'] ← applyC ctx g (← mkConstWithFreshMVarLevels ``PyTriple.exists_pre)
        | throwError "py_vcgen: internal — exists_pre"
      let nm := introNames[ni]? |>.getD (Name.mkSimple s!"x{ni}")
      let (_, g'') ← g'.intro nm
      g := g''
      ni := ni + 1
    else if body.isAppOfArity ``And 2 then
      let lhs := body.getArg! 0
      if lhs.isAppOfArity ``Exists 2 then
        let [g'] ← applyC ctx g (← mkConstWithFreshMVarLevels ``PyTriple.exists_and_pre)
          | throwError "py_vcgen: internal — exists_and_pre"
        let nm := introNames[ni]? |>.getD (Name.mkSimple s!"x{ni}")
        let (_, g'') ← g'.intro nm
        g := g''
        ni := ni + 1
      else if lhs.isAppOfArity ``And 2 then
        let [g'] ← applyC ctx g (← mkConstWithFreshMVarLevels ``PyTriple.and_assoc_pre)
          | throwError "py_vcgen: internal — and_assoc_pre"
        g := g'
      else if lhs.isAppOfArity ``Eq 3 then
        let [g'] ← applyC ctx g (← mkConstWithFreshMVarLevels ``PyTriple.eq_and_pre)
          | throwError "py_vcgen: internal — eq_and_pre"
        let (_, g'') ← g'.intro hypName
        return g''
      else
        throwError "py_vcgen: internal — unexpected precondition:{indentExpr body}"
    else
      throwError "py_vcgen: internal — unexpected precondition:{indentExpr body}"
  throwError "py_vcgen: internal — precondition normalization did not converge"

/-- Destructure an invariant hypothesis `∃ x₁ … tail, env = shape ∧ core`
(introducing the witnesses under `names` and the core under `hcore`), and
substitute the goal's `env` by the shape. The environment equation is
`subst`-eliminated — the same machinery the `init` path uses — rather than
merely rewritten into the target, so neither `env` nor the `heqE` equation
survives into residual goals' contexts. Used by the `htest`/`hexit`
obligation dischargers. -/
def destructInvHyp (g : MVarId) (hFv : FVarId) (names : Array Name) :
    MetaM MVarId := do
  let mut g := g
  let mut fv := hFv
  for n in names do
    let (_, restFv, g') ← casesTwo g fv n `hrest
    g := g'
    fv := restFv
  let (heqFv, _, g') ← casesTwo g fv `heqE `hcore
  Meta.subst g' heqFv

/-- Try to close an equation goal by `rfl` up to unfolding. -/
def tryRflClose (g : MVarId) : MetaM Bool := do
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let some (_, lhs, _) := t.eq? | return false
    try
      let gs ← g.apply (← mkEqRefl lhs)
      pure gs.isEmpty
    catch _ => pure false

/-! ### The `while` obligation dischargers -/

/-- Discharge `htest`: destructure the invariant, then verify by symbolic
execution that the test evaluates to `tv` at the shape. -/
def dischargeWhileTest (ctx : VCCtx) (g : MVarId) (slotNames : Array String) :
    MetaM Unit := do
  let (_, g) ← g.intro `env
  let (hFv, g) ← g.intro `hI
  let g ← destructInvHyp g hFv ((slotNames.map Name.mkSimple).push `tl)
  let [g] ← applyC ctx g
      (← g.withContext (appOpt ``EvalsTo.of_eval #[none, some (mkNatLit fuelK), none, none, none, none]))
    | throwError "py_vcgen: internal — of_eval"
  let ctx' ← g.withContext do addFacts ctx.pack.exec (← currentFacts)
  let r? ← try Prod.fst <$> Meta.simpGoal g ctx' ctx.pack.procs
    catch _ => pure (some (#[], g))
  match r? with
  | none => return
  | some (_, g) =>
    unless ← tryRflClose g do
      throwError "py_vcgen: could not verify the derived loop-test value (test outside the v1 recipe):{indentExpr (← g.withContext do instantiateMVars (← g.getType))}"

/-- Discharge `hexit`: destructure the invariant, normalize the negated
test, and re-establish the loop's exit condition by shape solving. -/
def dischargeWhileExit (ctx : VCCtx) (g : MVarId) (slotNames : Array String) :
    MetaM Unit := do
  let (_, g) ← g.intro `env
  let (hFv, g) ← g.intro `hI
  let g ← destructInvHyp g hFv ((slotNames.map Name.mkSimple).push `tl)
  let (hxFv, g) ← g.intro `hx
  let r? ← try Prod.fst <$> (Meta.simpGoal g ctx.pack.norm ctx.pack.procs
      (simplifyTarget := false) (fvarIdsToSimp := #[hxFv]))
    catch _ => pure (some (#[], g))
  match r? with
  | none => return
  | some (_, g) => closeByShape ctx g `exit

/-- Discharge the `if` rule's test hypothesis from the captured evaluation
and the two normalized truthiness facts. -/
def dischargeIfTest (ctx : VCCtx) (g : MVarId) (E V prfT : Lean.Expr)
    (tDead : Bool) (tNF : Lean.Expr) (tPrf? : Option Lean.Expr)
    (fDead : Bool) (fNF : Lean.Expr) (fPrf? : Option Lean.Expr) :
    MetaM Unit := do
  let (_, g) ← g.intro `env
  let (heqFv, g) ← g.intro `henv
  let g ← Meta.subst g heqFv
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    unless tgt.isAppOfArity ``Exists 2 do
      throwError "py_vcgen: internal — if-test goal:{indentExpr tgt}"
    let [g] ← applyC ctx g (mkApp3 (Lean.mkConst ``Exists.intro [.succ .zero])
        (Lean.mkConst ``Val) (tgt.getArg! 1) V)
      | throwError "py_vcgen: internal — if-test witness"
    let hEval ← appOpt ``EvalsTo.of_eval
      #[none, some (mkNatLit fuelK), none, none, none, some prfT]
    let truthyV := mkApp (Lean.mkConst ``truthy) V
    let mkImp (isTrue dead : Bool) (nf : Lean.Expr) (prf? : Option Lean.Expr) :
        MetaM Lean.Expr := do
      let _ := nf
      let hty := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) (Lean.mkConst ``Bool)
        truthyV (Lean.mkConst (if isTrue then ``Bool.true else ``Bool.false))
      withLocalDeclD `h hty fun h => do
        let hNorm ← match prf? with
          | some pp => mkEqMP pp h
          | none => pure h
        let body ← if dead then pure hNorm
          else mkAppM ``And.intro #[← mkEqRefl E, hNorm]
        mkLambdaFVars #[h] body
    let htImp ← mkImp true tDead tNF tPrf?
    let hfImp ← mkImp false fDead fNF fPrf?
    let gs ← applyC ctx g
      (← mkAppM ``And.intro #[hEval, ← mkAppM ``And.intro #[htImp, hfImp]])
    unless gs.isEmpty do
      throwError "py_vcgen: internal — if-test assembly"

/-- Residual tags of the top-level (whole-function) postcondition. -/
def topTags : PostTags :=
  { next := ⟨`ret, false⟩, ret := ⟨`ret, false⟩, brk := ⟨`ret, false⟩,
    cont := ⟨`ret, false⟩, err := ⟨`err, false⟩ }

/-! ### The walker -/

mutual

/-- Walk a `PyTriple` goal: chunk straight-line prefixes, dispatch the
first control statement, recurse on the continuation. -/
partial def walk (ctx : VCCtx) (tags : PostTags) (g : MVarId) : TacticM Unit := do
  let tg ← parseTripleGoal ctx g
  tg.g.withContext do
    let mut kinds : Array StmtKind := #[]
    for s in tg.stmts do kinds := kinds.push (← classify s)
    let mut firstCtrl : Option Nat := none
    for i in [0:tg.stmts.size] do
      if kinds[i]! == .term then break
      if kinds[i]! == .plain then continue
      firstCtrl := some i
      break
    match firstCtrl with
    | none => closeStraight ctx tags tg
    | some 0 =>
      match kinds[0]! with
      | .ctrlWhile => handleWhile ctx tags tg
      | .ctrlIf => handleIf ctx tags tg
      | .ctrlCall => handleCall ctx tags tg
      | _ => throwError "py_vcgen: internal — classification"
    | some k => splitPrefix ctx tags tg k

/-- Close a fully straight-line statement list by one captured run
(`PyTriple.of_exec`). -/
partial def closeStraight (ctx : VCCtx) (tags : PostTags) (tg : TripleGoal) :
    TacticM Unit := do
  let ssLit := mkStmtsLit tg.stmts
  let gs ← applyC ctx tg.g
    (← appOpt ``PyTriple.of_exec #[some tg.m, none, some ssLit, some tg.Q, none])
  let [g] := gs | throwError "py_vcgen: internal — of_exec goals"
  let (_, g) ← g.intro `env
  let (heqFv, g) ← g.intro `henv
  let g ← Meta.subst g heqFv
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    unless tgt.isAppOfArity ``Exists 2 do
      throwError "py_vcgen: internal — exec goal:{indentExpr tgt}"
    let [g] ← applyC ctx g (mkApp3 (Lean.mkConst ``Exists.intro [.succ .zero])
        (Lean.mkConst ``Nat) (tgt.getArg! 1) (mkNatLit fuelK))
      | throwError "py_vcgen: internal — fuel witness"
    let ty := (← instantiateMVars (← g.getType)).headBeta
    unless ty.isAppOfArity ``PyPost.holds 2 do
      throwError "py_vcgen: internal — holds goal:{indentExpr ty}"
    let (r, prf) ← captureRun ctx.pack (ty.getArg! 1)
    closeRun ctx tags g tg.Q r prf

/-- Discharge a straight-line prefix before a control point
(`PyTriple.run_seq`), then recurse. -/
partial def splitPrefix (ctx : VCCtx) (tags : PostTags) (tg : TripleGoal)
    (k : Nat) : TacticM Unit := do
  tg.g.withContext do
    let preLit := mkStmtsLit (tg.stmts.extract 0 k)
    let restLit := mkStmtsLit (tg.stmts.extract k tg.stmts.size)
    let (r, prf) ← captureRun ctx.pack
      (mkApp4 (Lean.mkConst ``execStmts) tg.m (mkNatLit fuelK) tg.E preLit)
    match ← parseRun r with
    | some (.next _) =>
      let term ← appOpt ``PyTriple.run_seq
        #[none, none, none, none, none, some restLit, some tg.Q, some prf, none]
      let [g2] ← applyC ctx tg.g term
        | throwError "py_vcgen: internal — run_seq goals"
      walk ctx tags g2
    | some _ => closeStraight ctx tags tg   -- the prefix escaped (raise)
    | none =>
      throwError "py_vcgen: symbolic execution of a straight-line prefix got stuck:{indentExpr r}"

/-- Handle a call statement `x = f(…)` / `(a, b) = f(…)`: evaluate the
arguments, find the callee's `CallsTo` fact, splice `EvalsTo.call` through
the generic assignment rule, continue from the updated environment. -/
partial def handleCall (ctx : VCCtx) (tags : PostTags) (tg : TripleGoal) :
    TacticM Unit := do
  tg.g.withContext do
    unless isNilTail tg.shape.tail && tg.shape.sets.isEmpty do
      throwError "py_vcgen: a call under a symbolic environment tail (inside a loop body) is outside the v1 tier"
    let s ← whnfR tg.stmts[0]!
    let tgtArr := s.getArg! 0
    let rhs ← whnfR (s.getArg! 1)
    let spA := s.getArg! 2
    let fnE ← whnfR (rhs.getArg! 0)
    let fnameE := fnE.getArg! 0
    let .lit (.strVal fname) ← whnfR fnameE
      | throwError "py_vcgen: callee name is not a literal"
    let spf := fnE.getArg! 1
    let argsArr := rhs.getArg! 1
    let spc := rhs.getArg! 3
    let (tgts, _) ← parseListLit (← arrToList tgtArr)
    let #[tgtE] := tgts
      | throwError "py_vcgen: chained assignment is outside the v0 tier"
    let (rL, prfL) ← captureRun ctx.pack
      (mkApp2 (Lean.mkConst ``Env.lookup) tg.E fnameE)
    unless (← whnfR rL).isAppOfArity ``Option.none 1 do
      throwError "py_vcgen: callee `{fname}` may be shadowed by a local binding"
    let (argEs, argTail) ← parseListLit (← arrToList argsArr)
    unless isNilTail argTail do
      throwError "py_vcgen: call-argument list is not literal"
    let exprTy := Lean.mkConst ``LeanModels.Python.Expr
    let argsListLit := mkListLit' exprTy argEs
      (mkApp (Lean.mkConst ``List.nil [Level.zero]) exprTy)
    let (rA, prfA) ← captureRun ctx.pack
      (mkApp4 (Lean.mkConst ``evalExprs) tg.m (mkNatLit fuelK) tg.E argsListLit)
    let rA' ← whnfR rA
    unless rA'.isAppOfArity ``Res.ok 2 do
      throwError "py_vcgen: call arguments did not evaluate:{indentExpr rA}"
    let vsLit := rA'.getArg! 1
    let some (factE, vE, sides) ← findCalleeFact ctx fname vsLit
      | throwError "py_vcgen: no `CallsTo` fact for callee `{fname}` at these arguments — bring a hypothesis into scope or register a `@[py_spec]` lemma"
    let (vr, _) ← Meta.simp vE ctx.pack.present ctx.pack.procs
    let (vNF, factE') ← match vr.proof? with
      | none => pure (vr.expr, factE)
      | some vp => do
        let factTy ← inferType factE
        pure (vr.expr, ← mkEqMP (← mkCongrArg factTy.appFn! vp) factE)
    let hargs ← mkAppM ``EvalsToList.of_eval #[prfA]
    let hcall ← appOpt ``EvalsTo.call
      #[some tg.m, some tg.E, some fnameE, some argsArr, some vsLit, some vNF,
        some spf, some spc, some prfL, some hargs, some factE']
    let (rAs, prfAs) ← captureRun ctx.pack
      (mkApp3 (Lean.mkConst ``assignTo) tg.E tgtE vNF)
    let rAs' ← whnfR rAs
    unless rAs'.isAppOfArity ``Res.ok 2 do
      throwError "py_vcgen: call-result assignment did not reduce:{indentExpr rAs}"
    let E'' := rAs'.getArg! 1
    let R ← mkEqPred E''
    let restLit := mkStmtsLit (tg.stmts.extract 1 tg.stmts.size)
    let seqT ← appOpt ``PyTriple.seq
      #[some tg.m, none, some R, some tg.Q, some tg.stmts[0]!, some restLit, none, none]
    let gs ← applyC ctx tg.g seqT
    let (g1, g2) ← splitSeqGoals gs
    let asnT ← appOpt ``PyStmtTriple.assign
      #[some tg.m, none, none, some tgtE, some (s.getArg! 1), some spA, none]
    let [gh] ← applyC ctx g1 asnT
      | throwError "py_vcgen: internal — assign rule"
    let (_, gh) ← gh.intro `env
    let (heqFv, gh) ← gh.intro `henv
    let gh ← Meta.subst gh heqFv
    gh.withContext do
      let t1 ← instantiateMVars (← gh.getType)
      let [gh] ← applyC ctx gh (mkApp3 (Lean.mkConst ``Exists.intro [.succ .zero])
          (Lean.mkConst ``Val) (t1.getArg! 1) vNF)
        | throwError "py_vcgen: internal — call witness v"
      let t2 := (← instantiateMVars (← gh.getType)).headBeta
      unless t2.isAppOfArity ``Exists 2 do
        throwError "py_vcgen: internal — call witness env goal:{indentExpr t2}"
      let [gh] ← applyC ctx gh (mkApp3 (Lean.mkConst ``Exists.intro [.succ .zero])
          envTy (t2.getArg! 1) E'')
        | throwError "py_vcgen: internal — call witness env"
      let gs' ← applyC ctx gh (← mkAppM ``And.intro
        #[hcall, ← mkAppM ``And.intro #[prfAs, ← mkEqRefl E'']])
      -- spec preconditions (side mvars inside the callee fact) resurface
      -- here as goals; discharge or push them as `side` residuals
      for sg in gs' do
        trySide ctx sg
    for sg in sides do
      trySide ctx sg
    walk ctx tags g2

/-- Handle an `if` statement: derive branch facts from the captured test
value, walk each live branch (straight-line, v1), fork the continuation on
the joined fall-through states. -/
partial def handleIf (ctx : VCCtx) (tags : PostTags) (tg : TripleGoal) :
    TacticM Unit := do
  tg.g.withContext do
    let s ← whnfR tg.stmts[0]!
    let testE := s.getArg! 0
    let bArr := s.getArg! 1
    let oArr := s.getArg! 2
    let spE := s.getArg! 3
    let (bStmts, _) ← parseListLit (← arrToList bArr)
    let (oStmts, _) ← parseListLit (← arrToList oArr)
    for br in #[bStmts, oStmts] do
      for st in br do
        match ← classify st with
        | .plain | .term => pure ()
        | _ => throwError "py_vcgen: `if` branches must be straight-line in v1 (no nested if/while/call)"
    let (rT, prfT) ← captureRun ctx.pack
      (mkApp4 (Lean.mkConst ``evalExpr) tg.m (mkNatLit fuelK) tg.E testE)
    let rT' ← whnfR rT
    unless rT'.isAppOfArity ``Res.ok 2 do
      closeStraight ctx tags tg   -- the test escaped (raise)
      return
    let V := rT'.getArg! 1
    let truthyV := mkApp (Lean.mkConst ``truthy) V
    let boolEq (b : Bool) : Lean.Expr :=
      mkApp3 (Lean.mkConst ``Eq [.succ .zero]) (Lean.mkConst ``Bool) truthyV
        (Lean.mkConst (if b then ``Bool.true else ``Bool.false))
    let (tNF, tPrf?) ← normProp ctx.pack (boolEq true)
    let (fNF, fPrf?) ← normProp ctx.pack (boolEq false)
    let tDead := tNF.isConstOf ``False
    let fDead := fNF.isConstOf ``False
    let mkEnvEq (a b : Lean.Expr) : Lean.Expr :=
      mkApp3 (Lean.mkConst ``Eq [.succ .zero]) envTy a b
    let mkBranchPre (dead : Bool) (nf : Lean.Expr) : MetaM Lean.Expr :=
      withLocalDeclD `env envTy fun env => do
        if dead then
          mkLambdaFVars #[env] (Lean.mkConst ``False)
        else
          mkLambdaFVars #[env] (mkAnd (mkEnvEq env tg.E) nf)
    let Pt ← mkBranchPre tDead tNF
    let Pf ← mkBranchPre fDead fNF
    let branchEnd (dead : Bool) (nf : Lean.Expr) (stmts : Array Lean.Expr) :
        TacticM (Option Lean.Expr) := do
      if dead then return none
      withLocalDeclD `hif nf fun _ => do
        let (r, _) ← captureRun ctx.pack (mkApp4 (Lean.mkConst ``execStmts)
          tg.m (mkNatLit fuelK) tg.E (mkStmtsLit stmts))
        match ← parseRun r with
        | some (.next Eb) => return some Eb
        | some _ => return none
        | none =>
          throwError "py_vcgen: symbolic execution of an `if` branch got stuck:{indentExpr r}"
    let tEnd ← branchEnd tDead tNF bStmts
    let fEnd ← branchEnd fDead fNF oStmts
    let join ← withLocalDeclD `env envTy fun env => do
      let mut parts : Array Lean.Expr := #[]
      if let some Eb := tEnd then
        parts := parts.push (mkAnd (mkEnvEq env Eb) tNF)
      if let some Eb := fEnd then
        parts := parts.push (mkAnd (mkEnvEq env Eb) fNF)
      let body :=
        if parts.size == 0 then Lean.mkConst ``False
        else if parts.size == 1 then parts[0]!
        else mkOr parts[0]! parts[1]!
      mkLambdaFVars #[env] body
    let restLit := mkStmtsLit (tg.stmts.extract 1 tg.stmts.size)
    let seqT ← appOpt ``PyTriple.seq
      #[some tg.m, none, some join, some tg.Q, some tg.stmts[0]!, some restLit, none, none]
    let gs ← applyC ctx tg.g seqT
    let (g1, g2) ← splitSeqGoals gs
    let Q1 ← g1.withContext do
      pure ((← instantiateMVars (← g1.getType)).getArg! 3)
    let ifT ← appOpt ``PyStmtTriple.ifStmt
      #[some tg.m, none, some Pt, some Pf, some Q1, some testE, some bArr,
        some oArr, some spE, none, none, none]
    let gsI ← applyC ctx g1 ifT
    let mut htest : Option MVarId := none
    let mut hb : Option MVarId := none
    let mut ho : Option MVarId := none
    for gg in gsI do
      let t ← instantiateMVars (← gg.getType)
      if t.isAppOf ``PyTriple then
        if hb.isNone && t.getArg! 1 == Pt then hb := some gg
        else ho := some gg
      else htest := some gg
    let (some gt, some gb, some go) := (htest, hb, ho)
      | throwError "py_vcgen: internal — ifStmt goals"
    dischargeIfTest ctx gt tg.E V prfT tDead tNF tPrf? fDead fNF fPrf?
    let doBranch (g : MVarId) (dead : Bool) : TacticM Unit := do
      if dead then
        let gs ← applyC ctx g (← mkConstWithFreshMVarLevels ``PyTriple.false_pre)
        unless gs.isEmpty do throwError "py_vcgen: internal — false_pre"
      else
        let g' ← normalizePre ctx #[] `hif g
        walk ctx tags g'
    doBranch gb tDead
    doBranch go fDead
    -- the continuation, forked on the join
    let .lam _ _ joinBody _ := join
      | throwError "py_vcgen: internal — join shape"
    if joinBody.isConstOf ``False then
      let gs ← applyC ctx g2 (← mkConstWithFreshMVarLevels ``PyTriple.false_pre)
      unless gs.isEmpty do throwError "py_vcgen: internal — false_pre join"
    else if joinBody.isAppOfArity ``Or 2 then
      let gsO ← applyC ctx g2 (← mkConstWithFreshMVarLevels ``PyTriple.or_pre)
      for gg in gsO do
        let g' ← normalizePre ctx #[] `hif gg
        walk ctx tags g'
    else
      let g' ← normalizePre ctx #[] `hif g2
      walk ctx tags g'

/-- Handle a `while` statement: build the invariant environment shape from
the clause pair (or delayed mvars), apply the layer-2 while rule through
`consequence`, discharge `htest`/`hexit`, walk the body per iteration, and
continue after the loop from the primed exit state. -/
partial def handleWhile (ctx : VCCtx) (tags : PostTags) (tg : TripleGoal) :
    TacticM Unit := do
  tg.g.withContext do
    let s ← whnfR tg.stmts[0]!
    let testE := s.getArg! 0
    let bArr := s.getArg! 1
    let oArr := s.getArg! 2
    let spE := s.getArg! 3
    let (oStmts, _) ← parseListLit (← arrToList oArr)
    unless oStmts.isEmpty do
      throwError "py_vcgen: `while … else:` is outside the v1 tier (layer-2 rule restriction)"
    let (bStmts, _) ← parseListLit (← arrToList bArr)
    let some li := ctx.loops.findIdx? (· == s)
      | throwError "py_vcgen: internal — loop not in pre-scan"
    let mut assigned : Array String := #[]
    for b in bStmts do assigned := assigned ++ (← stmtAssignedNames b)
    let allVars := tg.shape.entries ++ tg.shape.sets
    let slotEntries := allVars.filter (fun p => assigned.contains p.1)
    let slotNames := slotEntries.map (·.1)
    let hasBrk ← (bStmts.anyM stmtHasBreak : MetaM Bool)
    let exitT? := (ctx.exits.find? (·.1 == li)).map (·.2)
    let intTy := Lean.mkConst ``Int
    let (invU, decU, binders) ← do
      match ctx.clauses[li]? with
      | some (invT, decT) => do
        let invU ← instantiateMVars (← Term.withSynthesize (Term.elabTerm invT none))
        let decU ← instantiateMVars (← Term.withSynthesize (Term.elabTerm decT none))
        let bs := (lamBinderNames invU).map (·.toString)
        if bs.isEmpty then
          throwError "py_vcgen: `inv` must be an explicit lambda over the loop's Int variables"
        unless (lamBinderNames decU).size == bs.size do
          throwError "py_vcgen: `dec` must bind exactly the {bs.size} variables of `inv`"
        for b in bs do
          match slotEntries.find? (·.1 == b) with
          | none =>
            throwError "py_vcgen: invariant variable `{b}` is not an entry-environment variable assigned in this loop (assigned at entry: {slotNames})"
          | some (_, v) =>
            unless (← whnfR v).isAppOfArity ``Val.int 1 do
              throwError "py_vcgen: loop variable `{b}` is not `Val.int`-valued at loop entry"
        pure (invU, decU, bs.toList.toArray)
      | none => do
        match (← ctx.delayed.get).find? (·.1 == li) with
        | some (_, i, d) => pure (i, d, slotNames)
        | none => do
          for (n, v) in slotEntries do
            unless (← whnfR v).isAppOfArity ``Val.int 1 do
              throwError "py_vcgen: delayed clauses need Int-valued loop variables; `{n}` is not — give explicit clauses"
          let mut invTy : Lean.Expr := mkSort .zero
          let mut decTy : Lean.Expr := Lean.mkConst ``Nat
          for _ in slotNames do
            invTy ← mkArrow intTy invTy
            decTy ← mkArrow intTy decTy
          let invM ← mkFreshExprMVar invTy .syntheticOpaque
          let decM ← mkFreshExprMVar decTy .syntheticOpaque
          invM.mvarId!.setTag (Name.mkSimple s!"inv{li+1}")
          decM.mvarId!.setTag (Name.mkSimple s!"dec{li+1}")
          ctx.clauseGoals.modify (fun a => (a.push invM.mvarId!).push decM.mvarId!)
          ctx.delayed.modify (·.push (li, invM, decM))
          pure (invM, decM, slotNames)
    let exitInfo? : Option (Lean.Expr × Array String) ← do
      match exitT? with
      | some t => do
        let u ← instantiateMVars (← Term.withSynthesize (Term.elabTerm t none))
        let ebs := (lamBinderNames u).map (·.toString)
        for b in ebs do
          unless binders.contains b do
            throwError "py_vcgen: `exit` variable `{b}` must be one of the loop's `inv` binders ({binders})"
        pure (some (u, ebs))
      | none =>
        -- Delayed mode: a `break`-carrying loop needs its exit clause just
        -- as it needs `inv`/`dec` — request it as a goal (`exit<i>`) over
        -- the same binders instead of silently weakening the exit fact to
        -- the bare invariant. Clause mode (an `inv`/`dec` pair given for
        -- this loop, `exit` omitted) is unchanged.
        if ctx.clauses[li]?.isSome || !hasBrk then
          pure none
        else
          match (← ctx.delayedExits.get).find? (·.1 == li) with
          | some (_, e) => pure (some (e, binders))
          | none => do
            let mut exTy : Lean.Expr := mkSort .zero
            for _ in binders do
              exTy ← mkArrow intTy exTy
            let exM ← mkFreshExprMVar exTy .syntheticOpaque
            exM.mvarId!.setTag (Name.mkSimple s!"exit{li+1}")
            ctx.clauseGoals.modify (·.push exM.mvarId!)
            ctx.delayedExits.modify (·.push (li, exM))
            pure (some (exM, binders))
    let decls : Array (Name × (Array Lean.Expr → TacticM Lean.Expr)) :=
      (slotEntries.map (fun p =>
        (Name.mkSimple p.1,
         fun (_ : Array Lean.Expr) => pure (α := Lean.Expr)
           (if binders.contains p.1 then intTy else Lean.mkConst ``Val))))
      |>.push (`tl, fun _ => pure envTy)
    let (invE, μE, tvE, rE) ← withLocalDeclsD decls fun fvs => do
      let slotVars := fvs.extract 0 (fvs.size - 1)
      let tailFv := fvs[fvs.size - 1]!
      let slotVarOf (n : String) : Option Lean.Expr := do
        let i ← slotNames.findIdx? (· == n)
        slotVars[i]?
      let slotVal (n : String) (v : Lean.Expr) : Lean.Expr :=
        match slotVarOf n with
        | some x =>
          if binders.contains n then mkApp (Lean.mkConst ``Val.int) x else x
        | none => v
      let entries' := tg.shape.entries.map (fun (n, v) => (n, slotVal n v))
      let sets' := tg.shape.sets.map (fun (n, v) => (n, slotVal n v))
      let shapeE := mkEnvExpr { entries := entries', sets := sets', tail := tailFv }
      let clauseVars ← binders.mapM (fun b => do
        let some x := slotVarOf b
          | throwError "py_vcgen: internal — clause var `{b}`"
        pure x)
      let invApp := (mkAppN invU clauseVars).headBeta
      let mkEnvEq (env : Lean.Expr) : Lean.Expr :=
        mkApp3 (Lean.mkConst ``Eq [.succ .zero]) envTy env shapeE
      let invE ← withLocalDeclD `env envTy fun env => do
        mkLambdaFVars #[env] (← mkExistsNest fvs (mkAnd (mkEnvEq env) invApp))
      let μE ← withLocalDeclD `env envTy fun env => do
        let reads := binders.map fun b =>
          mkApp2 (Lean.mkConst ``envInt) env (mkStrLit b)
        mkLambdaFVars #[env] (mkAppN decU reads).headBeta
      unless ← isDefEq (← inferType μE) (← mkArrow envTy (Lean.mkConst ``Nat)) do
        throwError "py_vcgen: `dec` must return a `Nat` (write `(…).toNat`)"
      let (rV, _) ← captureRun ctx.pack
        (mkApp4 (Lean.mkConst ``evalExpr) tg.m (mkNatLit fuelK) shapeE testE)
      let rV' ← whnfR rV
      unless rV'.isAppOfArity ``Res.ok 2 do
        throwError "py_vcgen: the loop test did not evaluate at the invariant shape:{indentExpr rV}"
      let V := rV'.getArg! 1
      if V.containsFVar tailFv.fvarId! then
        throwError "py_vcgen: the loop test reads a variable first assigned inside the loop body — outside the v1 tier"
      for i in [0:slotVars.size] do
        unless binders.contains slotNames[i]! do
          if V.containsFVar slotVars[i]!.fvarId! then
            throwError "py_vcgen: the loop test reads assigned variable `{slotNames[i]!}` — add it to the `inv`/`dec` clause binders"
      let tvE ← withLocalDeclD `env envTy fun env => do
        let mut body := V
        for b in binders do
          if let some x := slotVarOf b then
            body := body.replaceFVar x
              (mkApp2 (Lean.mkConst ``envInt) env (mkStrLit b))
        mkLambdaFVars #[env] body
      let (exitNF, _) ← normProp ctx.pack
        (mkApp3 (Lean.mkConst ``Eq [.succ .zero]) (Lean.mkConst ``Bool)
          (mkApp (Lean.mkConst ``truthy) V) (Lean.mkConst ``Bool.false))
      let exitApp? ← exitInfo?.mapM fun (u, ebs) => do
        let vars ← ebs.mapM fun b => do
          let some x := slotVarOf b
            | throwError "py_vcgen: internal — exit var `{b}`"
          pure x
        pure (mkAppN u vars).headBeta
      let rE ← withLocalDeclD `env envTy fun env => do
        let core := match exitApp? with
          | some ea => mkAnd invApp ea
          | none => if hasBrk then invApp else mkAnd invApp exitNF
        mkLambdaFVars #[env] (← mkExistsNest fvs (mkAnd (mkEnvEq env) core))
      pure (invE, μE, tvE, rE)
    let restLit := mkStmtsLit (tg.stmts.extract 1 tg.stmts.size)
    let seqT ← appOpt ``PyTriple.seq
      #[some tg.m, none, some rE, some tg.Q, some tg.stmts[0]!, some restLit, none, none]
    let gs ← applyC ctx tg.g seqT
    let (g1, g2) ← splitSeqGoals gs
    let Q1 ← g1.withContext do
      pure ((← instantiateMVars (← g1.getType)).getArg! 3)
    let consT ← appOpt ``PyStmtTriple.consequence
      #[some tg.m, some invE, none, none, some Q1, some Q1, none, none, none]
    let gsC ← applyC ctx g1 consT
    let (h, hpre, hpost) ← splitConsGoals gsC
    let gsE ← applyC ctx hpost (← mkAppM ``PyPost.Entails.rfl #[Q1])
    unless gsE.isEmpty do throwError "py_vcgen: internal — Entails.rfl"
    let (_, gp) ← hpre.intro `env
    let (heqFv, gp) ← gp.intro `henv
    let gp ← Meta.subst gp heqFv
    closeByShape ctx gp `init
    let wT ← appOpt ``PyStmtTriple.whileLoop
      #[some tg.m, some testE, some bArr, some spE, some Q1, some invE,
        some μE, some tvE, none, none, none]
    let gsW ← applyC ctx h wT
    let mut htest : Option MVarId := none
    let mut hexit : Option MVarId := none
    let mut hbody : Option MVarId := none
    for gg in gsW do
      let cls ← gg.withContext do
        forallTelescope (← instantiateMVars (← gg.getType)) fun _ b => do
          let b ← instantiateMVars b
          if b.isAppOf ``EvalsTo then pure 0
          else if b.isAppOf ``PyTriple then pure 2
          else pure 1
      if cls == 0 then htest := some gg
      else if cls == 2 then hbody := some gg
      else hexit := some gg
    let (some gt, some gx, some gb) := (htest, hexit, hbody)
      | throwError "py_vcgen: internal — whileLoop goals"
    dischargeWhileTest ctx gt slotNames
    dischargeWhileExit ctx gx slotNames
    -- the body, per iteration
    let bodyTags : PostTags :=
      { next := ⟨`preserve, true⟩, ret := tags.ret, brk := ⟨`exit, false⟩,
        cont := ⟨`preserve, true⟩, err := tags.err }
    let (_, gb) ← gb.intro `n
    let gb ← normalizePre ctx ((slotNames.map Name.mkSimple).push `tl) `hAll gb
    let hAllFv ← findHyp gb `hAll
    let (hInvFv, _, gb) ← casesTwo gb hAllFv `hinv `hR
    let gb ← splitAndHyp gb hInvFv "hinv"
    let hRFv ← findHyp gb `hR
    let (hcFv, hmuFv, gb) ← casesTwo gb hRFv `hcont `hmu
    let r? ← try Prod.fst <$> (Meta.simpGoal gb ctx.pack.norm ctx.pack.procs
        (simplifyTarget := false) (fvarIdsToSimp := #[hcFv, hmuFv]))
      catch _ => pure (some (#[], gb))
    let gb ← match r? with
      | none => throwError "py_vcgen: internal — body hypotheses closed the goal"
      | some (_, gb) => pure gb
    let gb ← try
        Meta.subst gb (← findHyp gb `hmu)
      catch _ => pure gb
    walk ctx bodyTags gb
    -- after the loop, from the primed exit state
    let primed := (slotNames.map (fun n => Name.mkSimple (n ++ "'"))).push `tl'
    let g2 ← normalizePre ctx primed `hAll g2
    let hAllFv2 ← findHyp g2 `hAll
    let hasCont := exitInfo?.isSome || !hasBrk
    let g2 ←
      if hasCont then do
        let (hInvFv2, _, g2) ← casesTwo g2 hAllFv2 `hinv `hcont
        splitAndHyp g2 hInvFv2 "hinv"
      else
        splitAndHyp g2 hAllFv2 "hinv"
    walk ctx tags g2

end

/-! ### The elaborator -/

/-- Run the walker on the main goal (see the module docstring). -/
def runPyVcgen (progs : Array Ident) (clauses : Array (Term × Term))
    (exits : Array (Nat × Term)) : TacticM Unit := do
  withMainContext do
    let g ← getMainGoal
    let g ← normalizePyHyps g
    replaceMainGoal [g]
  withMainContext do
    let g ← getMainGoal
    let progNames ← progs.mapM fun p => realizeGlobalConstNoOverloadWithInfo p
    let pack ← mkPack progNames.toList
    let residuals ← IO.mkRef (#[] : Array MVarId)
    let clauseGoals ← IO.mkRef (#[] : Array MVarId)
    let delayed ← IO.mkRef (#[] : Array (Nat × Lean.Expr × Lean.Expr))
    let delayedExits ← IO.mkRef (#[] : Array (Nat × Lean.Expr))
    let tgt := (← instantiateMVars (← g.getType)).cleanupAnnotations
    if tgt.isAppOfArity ``CallsTo 4 then
      let m := tgt.getArg! 0
      let fnameE := tgt.getArg! 1
      let args := tgt.getArg! 2
      let v := tgt.getArg! 3
      let ctx0 : VCCtx :=
        { pack, mE := m, clauses, exits, loops := #[], residuals, clauseGoals,
          delayed, delayedExits }
      let (rF, prfF) ← captureRun pack
        (mkApp2 (Lean.mkConst ``findFunction) m fnameE)
      let rF' ← whnfR rF
      unless rF'.isAppOfArity ``Option.some 2 do
        throwError "py_vcgen: could not resolve the callee in the module (`findFunction` reduced to{indentExpr rF})"
      let fLit := rF'.getArg! 1
      let bridgeT ← appOpt ``PyTriple.callsTo
        #[some m, some fnameE, some fLit, some args, some v,
          none, none, none, none, none]
      let gs ← g.apply bridgeT
      let mut h : Option MVarId := none
      for gg in gs do
        let t ← instantiateMVars (← gg.getType)
        if t.isAppOf ``PyTriple then h := some gg
        else if t.isAppOfArity ``Eq 3 && (t.getArg! 1).isAppOf ``findFunction then
          let gs' ← gg.apply prfF
          unless gs'.isEmpty do throwError "py_vcgen: internal — findFunction goal"
        else
          closeRfl gg
      let some hGoal := h | throwError "py_vcgen: internal — bridge goals"
      let fLit' ← whnfR fLit
      let (bodyStmts, _) ← parseListLit (← arrToList (fLit'.getArg! 4))
      let ctx : VCCtx := { ctx0 with loops := ← collectLoops bodyStmts }
      walk ctx topTags hGoal
    else if tgt.isAppOfArity ``PyTriple 4 then
      let m := tgt.getArg! 0
      let (ss, _) ← parseListLit (tgt.getArg! 2)
      let ctx : VCCtx :=
        { pack, mE := m, clauses, exits, loops := ← collectLoops ss, residuals,
          clauseGoals, delayed, delayedExits }
      walk ctx topTags g
    else if tgt.isAppOfArity ``Exists 2 then
      -- `∃ v, CallsTo m f args v ∧ Φ v` — the relational bridge
      let .lam _ _ pBody _ := tgt.getArg! 1
        | throwError "py_vcgen: unsupported existential goal:{indentExpr tgt}"
      unless pBody.isAppOfArity ``And 2 do
        throwError "py_vcgen: an existential goal must be `∃ v, CallsTo … v ∧ Φ v`:{indentExpr tgt}"
      let c := pBody.getArg! 0
      unless c.isAppOfArity ``CallsTo 4 && c.getArg! 3 == .bvar 0 &&
          !(c.getArg! 0).hasLooseBVars && !(c.getArg! 1).hasLooseBVars &&
          !(c.getArg! 2).hasLooseBVars do
        throwError "py_vcgen: an existential goal must be `∃ v, CallsTo … v ∧ Φ v`:{indentExpr tgt}"
      let m := c.getArg! 0
      let fnameE := c.getArg! 1
      let ctx0 : VCCtx :=
        { pack, mE := m, clauses, exits, loops := #[], residuals, clauseGoals,
          delayed, delayedExits }
      let (rF, prfF) ← captureRun pack
        (mkApp2 (Lean.mkConst ``findFunction) m fnameE)
      let rF' ← whnfR rF
      unless rF'.isAppOfArity ``Option.some 2 do
        throwError "py_vcgen: could not resolve the callee in the module (`findFunction` reduced to{indentExpr rF})"
      let fLit := rF'.getArg! 1
      let bridgeT ← appOpt ``PyTriple.exists_callsTo
        #[some m, some fnameE, some fLit]
      let gs ← g.apply bridgeT
      let mut h : Option MVarId := none
      for gg in gs do
        let t ← instantiateMVars (← gg.getType)
        if t.isAppOf ``PyTriple then h := some gg
        else if t.isAppOfArity ``Eq 3 && (t.getArg! 1).isAppOf ``findFunction then
          let gs' ← gg.apply prfF
          unless gs'.isEmpty do throwError "py_vcgen: internal — findFunction goal"
        else
          closeRfl gg
      let some hGoal := h | throwError "py_vcgen: internal — bridge goals"
      let fLit' ← whnfR fLit
      let (bodyStmts, _) ← parseListLit (← arrToList (fLit'.getArg! 4))
      let ctx : VCCtx := { ctx0 with loops := ← collectLoops bodyStmts }
      walk ctx topTags hGoal
    else
      throwError "py_vcgen: the goal must be a `==>`/`⇓` (CallsTo) statement or a `PyTriple`:{indentExpr tgt}"
    let cg ← clauseGoals.get
    let rs ← residuals.get
    -- Number duplicate residual tags: `case preserve => …` silently takes
    -- only the FIRST of several same-tag goals, so a duplicated tag is a
    -- trap. The first same-tag goal keeps the bare tag (existing `case
    -- ret`/`case dec` uses and positional bullets stay valid); later ones
    -- get numbered variants (`preserve2`, `preserve3`, …), skipping any
    -- name already taken by a clause goal (a delayed `exit2`).
    let mut taken : Array Name := #[]
    for g in cg do taken := taken.push (← g.getTag)
    let mut tags : Array Name := #[]
    for g in rs do tags := tags.push (← g.getTag)
    let mut seen : Array Name := #[]
    for i in [0:rs.size] do
      let t := tags[i]!
      if seen.contains t then
        let mut j := 2
        let mut nm := Name.mkSimple s!"{t}{j}"
        while taken.contains nm || tags.contains nm || seen.contains nm do
          j := j + 1
          nm := Name.mkSimple s!"{t}{j}"
        rs[i]!.setTag nm
        seen := seen.push nm
      else
        seen := seen.push t
    replaceMainGoal (cg.toList ++ rs.toList)

end PyVCGen

open Lean Elab Tactic PyVCGen in
/-- One `py_vcgen` loop clause: `(inv := …)` / `(dec := …)` (labels may
carry indices: `inv1`, `dec2`, …). -/
syntax pyVcgenClause := " (" ident " := " term ")"

open Lean Elab Tactic PyVCGen in
/-- `py_vcgen [prog] (inv := fun (x y : Int) => …) (dec := fun (x y : Int) => …) …`
— the VC-generating walker (module docstring): bridge a `==>`/`⇓`
(`CallsTo`) or `PyTriple` goal to the function-body triple and walk it,
discharging every interpreter obligation; the i-th `inv`/`dec` clause pair
instantiates the i-th `while` (source order). With clauses omitted the
invariants/measures are left as delayed goals `inv1`/`dec1`/… (mvcgen
style), plus `exit<i>` for a `break`-carrying loop. Residual goals are
pure mathematics over named atoms, tagged
`init`/`preserve`/`dec`/`exit`/`ret`/`err`/`side` (same-tag duplicates
numbered: `preserve`, `preserve2`, …). -/
elab "py_vcgen" "[" progs:ident,+ "]" cls:pyVcgenClause* : tactic => do
  let mut invs : Array Term := #[]
  let mut decs : Array Term := #[]
  let mut exits : Array (Nat × Term) := #[]
  for c in cls do
    match c with
    | `(pyVcgenClause| ($id:ident := $t:term)) =>
      let s := id.getId.toString
      if s.startsWith "exit" then
        let sfx := s.drop 4
        let some idx := (if sfx.isEmpty then some 1 else sfx.toNat?)
          | throwErrorAt id "py_vcgen: `exit` labels carry the loop number (`exit`, `exit2`, …)"
        exits := exits.push (idx - 1, t)
      else if s.startsWith "inv" then invs := invs.push t
      else if s.startsWith "dec" then decs := decs.push t
      else throwErrorAt id "py_vcgen: clause labels must start with `inv`, `dec` or `exit`"
    | _ => throwUnsupportedSyntax
  unless invs.size == decs.size do
    throwError "py_vcgen: {invs.size} `inv` clause(s) but {decs.size} `dec` clause(s)"
  runPyVcgen progs.getElems (invs.zip decs) exits

/-! ## Smoke tests

A straight-line function (walker closes outright), a countdown loop in
clause form, and the same loop in delayed-clause form. `#py_check` pins the
concrete runs (non-vacuity). Heavier shapes (nested loops with break, env
growth, calls) are exercised by the validation gallery. -/

section SmokeTest

private def vSp : Span := ⟨0, 0, 0, 0⟩

/-- `def sl(x): y = x + 4 ⏎ return x * y` -/
private def slFn : FunctionDefn where
  name := "sl"
  params := #[⟨"x", vSp⟩]
  argsOk := true
  body := #[
    .assign #[.name "y" vSp]
      (.binOp (.name "x" vSp) .add (.constant (.int 4) vSp) vSp) vSp,
    .ret (some (.binOp (.name "x" vSp) .mult (.name "y" vSp) vSp)) vSp]
  span := vSp

/-- `def cd(n): i = n ⏎ while 0 < i: i = i - 1 ⏎ return i` -/
private def cdFn : FunctionDefn where
  name := "cd"
  params := #[⟨"n", vSp⟩]
  argsOk := true
  body := #[
    .assign #[.name "i" vSp] (.name "n" vSp) vSp,
    .whileLoop (.compare (.constant (.int 0) vSp) #[.lt] #[.name "i" vSp] vSp)
      #[.assign #[.name "i" vSp]
          (.binOp (.name "i" vSp) .sub (.constant (.int 1) vSp) vSp) vSp]
      #[] vSp,
    .ret (some (.name "i" vSp)) vSp]
  span := vSp

private def vcgenM : Module := { functions := #[slFn, cdFn], topLevel := #[] }

#py_check vcgenM.sl(3) = 21
#py_check vcgenM.cd(5) = 0

/-- Straight-line: the walker closes the goal with no residuals. -/
example : CallsTo vcgenM "sl" #[.int 3] (.int 21) := by
  py_vcgen [vcgenM, slFn, cdFn]

/-- Clause form: only arithmetic residuals remain. -/
example : CallsTo vcgenM "cd" #[.int 5] (.int 0) := by
  py_vcgen [vcgenM, slFn, cdFn] (inv := fun (i : Int) => 0 ≤ i)
                    (dec := fun (i : Int) => i.toNat)
  all_goals omega

/-- Delayed-clause (mvcgen-style) form: assign `inv1`/`dec1`, then the same
residuals. -/
example : CallsTo vcgenM "cd" #[.int 3] (.int 0) := by
  py_vcgen [vcgenM, slFn, cdFn]
  case inv1 => exact fun i => 0 ≤ i
  case dec1 => exact fun i => i.toNat
  all_goals omega

end SmokeTest

end LeanModels.Python
