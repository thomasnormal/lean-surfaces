import LeanModels.Python.Obs

/-!
# Flow-aware triples (`py_vcgen` layer 1: `PyPost` / `PyTriple`)

The v2 proof layer's foundation: a TOTAL-correctness Hoare triple over the
interpreter's statement level, with a *flow-aware* postcondition. This file is
additive — nothing in the existing surface (`py_prove`/`py_begin`/`py_loop`,
the arrows) changes; later phases bridge triples to `CallsTo` and grow a vcgen
tactic on top of the rules here.

Design (the settled forks, recorded):

* **`PyPost` mirrors `Std.Do`'s `PostCond`-with-shapes idea** specialized to
  our `Flow`: one arm per way a statement list can land — `next` (fall
  through), `ret` (a `return` escaped), `brk`/`cont` (a loop-control flow
  escaped, consumed by an enclosing loop rule), plus an **`err` arm for
  `PyErr`** (the analog of `Std.Do`'s `except` barrels). The `err` arm is
  included NOW, so raise-specs become first-class triples later without
  restating every rule; its cost — every rule carries it — is paid once here
  by threading it unchanged, and its default is `False`, so straight-line
  specs never mention it. `Res.unsupported` gets NO arm: it lands in `False`,
  making a triple about an out-of-tier program unprovable — loud by
  construction. `Res.timeout` also lands in `False`: with the threshold
  quantifier below this is what makes the triple *total* correctness.

* **`PyTriple` is in fuel-threshold form** (`∃ t, ∀ F ≥ t, …`), not bare
  `∃ fuel` — the shape `fuelMono` composes: `PyTriple.exec` extracts a
  *decided result pinned at every larger fuel*, which is exactly what the
  `seq`/`ifStmt` proofs splice at whatever fuel the surrounding symbolic
  execution produces (the `egcd_loop`/`execWhile_at_least` recipe, with the
  `max`-of-thresholds bookkeeping replaced by sums + `omega`). Introduction
  needs only a single-fuel witness (`PyTriple.of_exec`); monotonicity supplies
  the threshold.

* **Two levels, one postcondition type.** `PyStmtTriple` (one `Stmt`, over
  `execStmt`) is the workhorse the per-statement rules conclude;
  `PyTriple` (a `List Stmt`, over `execStmts`) is the judgment specs quote.
  `PyTriple.seq` composes a statement triple whose `next` arm is the
  midcondition with a list triple for the rest — non-`next` arms bypass the
  rest, exactly as `execStmts` short-circuits, so `seq` is the *only* place
  flow-routing logic lives.

* **Expression interface: `EvalsTo`** — `∃ fuel`-form like `CallsTo`, with an
  `at_least` threshold accessor (house convention, Obs.lean). Rules take
  `EvalsTo` hypotheses per environment (`∀ env, P env → ∃ v, EvalsTo … ∧ …`,
  the wp shape); discharge them at concrete environments by `EvalsTo.of_eval`
  + `rfl`/`py_simp`, or later by a vcgen-computed threshold.

Rule inventory: `PyTriple.nil`/`.seq`/`.single`/`.consequence`/`.frame`;
`PyStmtTriple.pass`/`.ret`/`.retNone`/`.brk`/`.cont`/`.exprStmt`/`.assign`
(generic `assignTo` target)/`.assignName`/`.augAssign`/`.ifStmt`/
`.consequence`. The `while` rule (generalizing `execWhile_total_of_invariant`,
Surface.lean) is deliberately NOT here — it lives in VC2.lean
(`PyStmtTriple.whileLoop`, with the call rules, the `@[py_spec]` registry,
and the arrow⇄triple bridges), consuming the `brk`/`cont` arms this file
plumbs.
-/

namespace LeanModels.Python

/-! ## `PyPost` — the flow-aware postcondition -/

/-- Flow-aware postcondition of a statement list: one arm per landing.
`next` is the main arm (fall through, environment transformed); `ret` sees
the returned value and the final environment; `brk`/`cont` are consumed by
an enclosing loop rule; `err` (default `False`) makes raise-specs stateable
— it mirrors `Std.Do.PostCond`'s exception barrels, specialized to `PyErr`
(no environment: the interpreter's `Res.exn` carries none). `timeout` and
`unsupported` have no arms — see `PyPost.holds`. -/
structure PyPost where
  /-- The statements fell through normally (`Flow.next`). -/
  next : Env → Prop
  /-- A `return` escaped with this value (`Flow.ret`). -/
  ret : Val → Env → Prop := fun _ _ => False
  /-- A `break` escaped (`Flow.brk`) — consumed by an enclosing loop rule. -/
  brk : Env → Prop := fun _ => False
  /-- A `continue` escaped (`Flow.cont`) — consumed by an enclosing loop rule. -/
  cont : Env → Prop := fun _ => False
  /-- The run raised this Python error (`Res.exn`). Default `False`: plain
  total-correctness specs assert error-freedom without mentioning it. -/
  err : PyErr → Prop := fun _ => False

namespace PyPost

/-- Does an interpreter result land in the arm the postcondition prescribes?
`timeout` is `False` (the triple's threshold shape then *excludes* it: total
correctness); `unsupported` is `False` (out-of-tier programs admit no triple
— loud by construction, cf. `Obs.stuck` being distinct from `diverges`). -/
def holds (Q : PyPost) : Res (Env × Flow) → Prop
  | .ok (env, .next) => Q.next env
  | .ok (env, .ret v) => Q.ret v env
  | .ok (env, .brk) => Q.brk env
  | .ok (env, .cont) => Q.cont env
  | .exn e => Q.err e
  | .timeout => False
  | .unsupported _ => False

@[simp] theorem holds_ok_next (Q : PyPost) (env : Env) :
    Q.holds (.ok (env, .next)) = Q.next env := rfl
@[simp] theorem holds_ok_ret (Q : PyPost) (env : Env) (v : Val) :
    Q.holds (.ok (env, .ret v)) = Q.ret v env := rfl
@[simp] theorem holds_ok_brk (Q : PyPost) (env : Env) :
    Q.holds (.ok (env, .brk)) = Q.brk env := rfl
@[simp] theorem holds_ok_cont (Q : PyPost) (env : Env) :
    Q.holds (.ok (env, .cont)) = Q.cont env := rfl
@[simp] theorem holds_exn (Q : PyPost) (e : PyErr) :
    Q.holds (.exn e) = Q.err e := rfl
@[simp] theorem holds_timeout (Q : PyPost) :
    Q.holds .timeout = False := rfl
@[simp] theorem holds_unsupported (Q : PyPost) (msg : String) :
    Q.holds (.unsupported msg) = False := rfl

/-- A result landing in an arm is decided — the hook that lets `fuelMono`
pin it at every larger fuel (`PyTriple.exec`). -/
theorem holds_ne_timeout {Q : PyPost} {r : Res (Env × Flow)}
    (h : Q.holds r) : r ≠ .timeout := fun ht => by subst ht; exact h

/-- Postcondition of code that falls through normally into `Q` — every other
arm `False` (straight-line statement lists between control constructs). -/
def ofNext (Q : Env → Prop) : PyPost := { next := Q }

/-- Postcondition of code that always `return`s into `Q` — every other arm
`False` (the function-body shape the `CallsTo` bridge will consume). -/
def ofRet (Q : Val → Env → Prop) : PyPost := { next := fun _ => False, ret := Q }

/-- Arm-wise entailment `Q → Q'` — the postcondition side of
`PyTriple.consequence`. -/
structure Entails (Q Q' : PyPost) : Prop where
  next : ∀ env, Q.next env → Q'.next env
  ret : ∀ v env, Q.ret v env → Q'.ret v env
  brk : ∀ env, Q.brk env → Q'.brk env
  cont : ∀ env, Q.cont env → Q'.cont env
  err : ∀ e, Q.err e → Q'.err e

theorem Entails.rfl (Q : PyPost) : Entails Q Q :=
  ⟨fun _ h => h, fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

/-- Entailment transports `holds` — result-shape-agnostic weakening. -/
theorem Entails.holds {Q Q' : PyPost} (h : Entails Q Q') :
    ∀ {r : Res (Env × Flow)}, Q.holds r → Q'.holds r
  | .ok (env, .next), hr => h.next env hr
  | .ok (env, .ret v), hr => h.ret v env hr
  | .ok (env, .brk), hr => h.brk env hr
  | .ok (env, .cont), hr => h.cont env hr
  | .exn e, hr => h.err e hr
  | .timeout, hr => hr.elim
  | .unsupported _, hr => hr.elim

/-- Conjoin a pure (environment-independent) proposition onto every arm —
the postcondition side of `PyTriple.frame`. -/
def and (Q : PyPost) (R : Prop) : PyPost where
  next env := Q.next env ∧ R
  ret v env := Q.ret v env ∧ R
  brk env := Q.brk env ∧ R
  cont env := Q.cont env ∧ R
  err e := Q.err e ∧ R

theorem holds_and {Q : PyPost} {R : Prop} {r : Res (Env × Flow)}
    (h : Q.holds r) (hR : R) : (Q.and R).holds r := by
  match r with
  | .ok (env, .next) | .ok (env, .ret v) | .ok (env, .brk) | .ok (env, .cont)
  | .exn e => exact ⟨h, hR⟩
  | .timeout | .unsupported _ => exact h.elim

end PyPost

/-! ## The expression-evaluation interface -/

/-- Terminating expression evaluation: *some* fuel evaluates `e` to `v` in
`env` — the expression-level `CallsTo` (same `∃ fuel` shape, same `at_least`
threshold accessor). This is the hypothesis form every rule takes for its
embedded expressions; discharge at a concrete environment with
`EvalsTo.of_eval` + `rfl` (or `py_simp`), at a symbolic one by whatever
computes the evaluation. -/
def EvalsTo (m : Module) (env : Env) (e : Expr) (v : Val) : Prop :=
  ∃ fuel, evalExpr m fuel env e = .ok v

/-- Introduce `EvalsTo` from one concrete run (any fuel — monotonicity is
`at_least`'s job, not the introduction's). -/
theorem EvalsTo.of_eval {m : Module} {fuel : Nat} {env : Env} {e : Expr}
    {v : Val} (h : evalExpr m fuel env e = .ok v) : EvalsTo m env e v :=
  ⟨fuel, h⟩

/-- Fuel-threshold form of an `EvalsTo` fact (the `CallsTo.at_least` analog):
the evaluation succeeds at *every* sufficiently large fuel. Every rule below
consumes its expression hypotheses through this. -/
theorem EvalsTo.at_least {m : Module} {env : Env} {e : Expr} {v : Val}
    (h : EvalsTo m env e v) :
    ∃ t, ∀ F ≥ t, evalExpr m F env e = .ok v := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, fun F hF => evalExpr_mono hf (by simp) F hF⟩

/-! ## The triples -/

/-- Statement-level total-correctness triple: from any environment satisfying
`P`, some fuel threshold `t` makes `execStmt` land in the arm `Q` prescribes
at *every* fuel `F ≥ t` (timeout is thereby excluded — total correctness;
`unsupported` is excluded because no arm accepts it). The per-statement
structural rules conclude this; `PyTriple.seq` consumes it. -/
def PyStmtTriple (m : Module) (P : Env → Prop) (s : Stmt) (Q : PyPost) : Prop :=
  ∀ env, P env → ∃ t, ∀ F ≥ t, Q.holds (execStmt m F env s)

/-- **The triple of the py_vcgen layer**: total correctness of a statement
list, threshold form (see `PyStmtTriple`; same shape one level up, over
`execStmts`). The threshold quantifier is what makes triples compose by
`fuelMono`: `PyTriple.exec` extracts a single decided result valid at every
larger fuel, spliceable wherever the surrounding execution lands. -/
def PyTriple (m : Module) (P : Env → Prop) (ss : List Stmt) (Q : PyPost) : Prop :=
  ∀ env, P env → ∃ t, ∀ F ≥ t, Q.holds (execStmts m F env ss)

/-- Destructure a nonzero-threshold bound: `F ≥ t + 1` is a successor
`F' + 1` with `F' ≥ t` — the one-step unfold shape every rule proof uses
(the interpreter matches fuel first). -/
private theorem succ_le_dest {t F : Nat} (h : t + 1 ≤ F) :
    ∃ F', F = F' + 1 ∧ t ≤ F' := ⟨F - 1, by omega, by omega⟩

/-- Extraction (the composability engine): a statement triple yields, per
`P`-environment, one *decided* result in `Q`'s arm together with a threshold
pinning `execStmt` to it at every larger fuel — `holds_ne_timeout` +
`execStmt_mono` (FuelMono). Rules splice this at whatever fuel their own
symbolic execution produces, side conditions by `omega`. -/
theorem PyStmtTriple.exec {m : Module} {P : Env → Prop} {s : Stmt} {Q : PyPost}
    (h : PyStmtTriple m P s Q) {env : Env} (hP : P env) :
    ∃ r t, Q.holds r ∧ ∀ F ≥ t, execStmt m F env s = r := by
  obtain ⟨t, ht⟩ := h env hP
  have h0 := ht t (Nat.le_refl t)
  exact ⟨_, t, h0, execStmt_mono rfl (PyPost.holds_ne_timeout h0)⟩

/-- Extraction at the list level — see `PyStmtTriple.exec`. -/
theorem PyTriple.exec {m : Module} {P : Env → Prop} {ss : List Stmt} {Q : PyPost}
    (h : PyTriple m P ss Q) {env : Env} (hP : P env) :
    ∃ r t, Q.holds r ∧ ∀ F ≥ t, execStmts m F env ss = r := by
  obtain ⟨t, ht⟩ := h env hP
  have h0 := ht t (Nat.le_refl t)
  exact ⟨_, t, h0, execStmts_mono rfl (PyPost.holds_ne_timeout h0)⟩

/-- Introduction from a single-fuel witness per environment: one decided run
in the right arm suffices — `execStmt_mono` supplies the threshold. -/
theorem PyStmtTriple.of_exec {m : Module} {P : Env → Prop} {s : Stmt}
    {Q : PyPost} (h : ∀ env, P env → ∃ fuel, Q.holds (execStmt m fuel env s)) :
    PyStmtTriple m P s Q := by
  intro env hP
  obtain ⟨fuel, hf⟩ := h env hP
  refine ⟨fuel, fun F hF => ?_⟩
  rw [execStmt_mono rfl (PyPost.holds_ne_timeout hf) F hF]
  exact hf

/-- Introduction from a single-fuel witness — see `PyStmtTriple.of_exec`. -/
theorem PyTriple.of_exec {m : Module} {P : Env → Prop} {ss : List Stmt}
    {Q : PyPost} (h : ∀ env, P env → ∃ fuel, Q.holds (execStmts m fuel env ss)) :
    PyTriple m P ss Q := by
  intro env hP
  obtain ⟨fuel, hf⟩ := h env hP
  refine ⟨fuel, fun F hF => ?_⟩
  rw [execStmts_mono rfl (PyPost.holds_ne_timeout hf) F hF]
  exact hf

/-! ## Structural rules — list level -/

/-- Empty list: falls through with the environment untouched, so the `next`
arm must hold outright (the Hoare `skip`). -/
theorem PyTriple.nil {m : Module} {P : Env → Prop} {Q : PyPost}
    (h : ∀ env, P env → Q.next env) : PyTriple m P [] Q := by
  intro env hP
  refine ⟨1, fun F hF => ?_⟩
  obtain ⟨F', rfl, -⟩ := succ_le_dest hF
  simpa [execStmts] using h env hP

/-- **Sequencing** — the composition rule and the only place flow routing
lives: run `s` under a postcondition whose `next` arm is the midcondition
`R`, then the rest from `R`; every non-`next` arm of `Q` passes through `s`
directly, bypassing `rest`, exactly as `execStmts` short-circuits (mirror of
`Std.Do`'s bind-spec threading its exception conditions unchanged).
Thresholds compose by splicing the two extracted runs at a summed bound —
`fuelMono` under the hood, `omega` for the arithmetic. -/
theorem PyTriple.seq {m : Module} {P R : Env → Prop} {Q : PyPost} {s : Stmt}
    {rest : List Stmt} (h1 : PyStmtTriple m P s { Q with next := R })
    (h2 : PyTriple m R rest Q) : PyTriple m P (s :: rest) Q := by
  intro env hP
  obtain ⟨r1, t1, hr1, hstep1⟩ := h1.exec hP
  cases r1 with
  | ok p =>
    obtain ⟨env', flow⟩ := p
    cases flow with
    | next =>
      obtain ⟨r2, t2, hr2, hstep2⟩ := h2.exec (show R env' from hr1)
      refine ⟨t1 + t2 + 1, fun F hF => ?_⟩
      obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
      simpa [execStmts, hstep1 F' (by omega), hstep2 F' (by omega)] using hr2
    | ret v =>
      refine ⟨t1 + 1, fun F hF => ?_⟩
      obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
      simpa [execStmts, hstep1 F' hF'] using hr1
    | brk =>
      refine ⟨t1 + 1, fun F hF => ?_⟩
      obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
      simpa [execStmts, hstep1 F' hF'] using hr1
    | cont =>
      refine ⟨t1 + 1, fun F hF => ?_⟩
      obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
      simpa [execStmts, hstep1 F' hF'] using hr1
  | exn e =>
    refine ⟨t1 + 1, fun F hF => ?_⟩
    obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
    simpa [execStmts, hstep1 F' hF'] using hr1
  | timeout => exact (PyPost.holds_ne_timeout hr1 rfl).elim
  | unsupported msg => exact hr1.elim

/-- Singleton list from a statement triple (`seq` against `nil`; the
midcondition is `Q.next` itself, closed by structure eta). -/
theorem PyTriple.single {m : Module} {P : Env → Prop} {s : Stmt} {Q : PyPost}
    (h : PyStmtTriple m P s Q) : PyTriple m P [s] Q :=
  PyTriple.seq (R := Q.next) h (PyTriple.nil fun _ hQ => hQ)

/-- Consequence: strengthen the precondition, weaken every arm. -/
theorem PyTriple.consequence {m : Module} {P P' : Env → Prop} {ss : List Stmt}
    {Q Q' : PyPost} (h : PyTriple m P ss Q) (hpre : ∀ env, P' env → P env)
    (hpost : Q.Entails Q') : PyTriple m P' ss Q' := by
  intro env hP
  obtain ⟨t, ht⟩ := h env (hpre env hP)
  exact ⟨t, fun F hF => hpost.holds (ht F hF)⟩

/-- Consequence at the statement level — see `PyTriple.consequence`. -/
theorem PyStmtTriple.consequence {m : Module} {P P' : Env → Prop} {s : Stmt}
    {Q Q' : PyPost} (h : PyStmtTriple m P s Q) (hpre : ∀ env, P' env → P env)
    (hpost : Q.Entails Q') : PyStmtTriple m P' s Q' := by
  intro env hP
  obtain ⟨t, ht⟩ := h env (hpre env hP)
  exact ⟨t, fun F hF => hpost.holds (ht F hF)⟩

/-- Frame a *pure* proposition through a triple: `R` rides along into every
arm. Only environment-independent framing is offered — statements mutate the
environment, so an env-dependent frame would be unsound in general (a
separation-logic-style footprint discipline is a later phase's concern). -/
theorem PyTriple.frame {m : Module} {P : Env → Prop} {ss : List Stmt}
    {Q : PyPost} (R : Prop) (h : PyTriple m P ss Q) :
    PyTriple m (fun env => P env ∧ R) ss (Q.and R) := by
  intro env hPR
  obtain ⟨t, ht⟩ := h env hPR.1
  exact ⟨t, fun F hF => PyPost.holds_and (ht F hF) hPR.2⟩

/-! ## Structural rules — statement level

Each rule is proved against the interpreter by one-step symbolic execution:
destructure the threshold bound to expose a successor fuel (`succ_le_dest`),
unfold `execStmt` at it, splice the expression runs (threshold form,
`omega` side conditions), and land in the prescribed arm. Hypotheses are in
wp shape — `∀ env, P env → ∃ …value…, EvalsTo … ∧ <arm at the new env>` —
so a vcgen tactic can compute them outside-in. -/

/-- `pass`: falls through, environment untouched. -/
theorem PyStmtTriple.pass {m : Module} {P : Env → Prop} {Q : PyPost} {sp : Span}
    (h : ∀ env, P env → Q.next env) : PyStmtTriple m P (.pass sp) Q := by
  intro env hP
  refine ⟨1, fun F hF => ?_⟩
  obtain ⟨F', rfl, -⟩ := succ_le_dest hF
  simpa [execStmt] using h env hP

/-- `break`: discharges into the `brk` arm. -/
theorem PyStmtTriple.brk {m : Module} {P : Env → Prop} {Q : PyPost} {sp : Span}
    (h : ∀ env, P env → Q.brk env) : PyStmtTriple m P (.brk sp) Q := by
  intro env hP
  refine ⟨1, fun F hF => ?_⟩
  obtain ⟨F', rfl, -⟩ := succ_le_dest hF
  simpa [execStmt] using h env hP

/-- `continue`: discharges into the `cont` arm. -/
theorem PyStmtTriple.cont {m : Module} {P : Env → Prop} {Q : PyPost} {sp : Span}
    (h : ∀ env, P env → Q.cont env) : PyStmtTriple m P (.cont sp) Q := by
  intro env hP
  refine ⟨1, fun F hF => ?_⟩
  obtain ⟨F', rfl, -⟩ := succ_le_dest hF
  simpa [execStmt] using h env hP

/-- Bare `return`: discharges into the `ret` arm at `Val.none`. -/
theorem PyStmtTriple.retNone {m : Module} {P : Env → Prop} {Q : PyPost}
    {sp : Span} (h : ∀ env, P env → Q.ret .none env) :
    PyStmtTriple m P (.ret Option.none sp) Q := by
  intro env hP
  refine ⟨1, fun F hF => ?_⟩
  obtain ⟨F', rfl, -⟩ := succ_le_dest hF
  simpa [execStmt] using h env hP

/-- `return e`: evaluate `e`, discharge into the `ret` arm at its value. -/
theorem PyStmtTriple.ret {m : Module} {P : Env → Prop} {Q : PyPost} {e : Expr}
    {sp : Span} (h : ∀ env, P env → ∃ v, EvalsTo m env e v ∧ Q.ret v env) :
    PyStmtTriple m P (.ret (some e) sp) Q := by
  intro env hP
  obtain ⟨v, hv, hQ⟩ := h env hP
  obtain ⟨t, ht⟩ := hv.at_least
  refine ⟨t + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  simpa [execStmt, ht F' hF'] using hQ

/-- Expression statement: evaluate for effect-freedom (v0 expressions cannot
mutate), fall through with the environment untouched. -/
theorem PyStmtTriple.exprStmt {m : Module} {P : Env → Prop} {Q : PyPost}
    {e : Expr} {sp : Span}
    (h : ∀ env, P env → ∃ v, EvalsTo m env e v ∧ Q.next env) :
    PyStmtTriple m P (.exprStmt e sp) Q := by
  intro env hP
  obtain ⟨v, hv, hQ⟩ := h env hP
  obtain ⟨t, ht⟩ := hv.at_least
  refine ⟨t + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  simpa [execStmt, ht F' hF'] using hQ

/-- Single-target assignment, generic over the target: evaluate the value,
store it with the pure helper `assignTo` (which handles both `Name` and
tuple-unpacking targets — the `assignTo … = .ok env'` hypothesis is
discharged by `rfl`/`py_simp` at concrete targets), fall through at the
updated environment. -/
theorem PyStmtTriple.assign {m : Module} {P : Env → Prop} {Q : PyPost}
    {tgt e : Expr} {sp : Span}
    (h : ∀ env, P env → ∃ v env', EvalsTo m env e v ∧
        assignTo env tgt v = .ok env' ∧ Q.next env') :
    PyStmtTriple m P (.assign #[tgt] e sp) Q := by
  intro env hP
  obtain ⟨v, env', hv, ha, hQ⟩ := h env hP
  obtain ⟨t, ht⟩ := hv.at_least
  refine ⟨t + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  simpa [execStmt, ht F' hF', ha] using hQ

/-- `x = e` (the `Name`-target special case, `assignTo` pre-reduced): fall
through at `Env.set env x v`. -/
theorem PyStmtTriple.assignName {m : Module} {P : Env → Prop} {Q : PyPost}
    {x : String} {e : Expr} {sp sp' : Span}
    (h : ∀ env, P env → ∃ v, EvalsTo m env e v ∧ Q.next (Env.set env x v)) :
    PyStmtTriple m P (.assign #[.name x sp] e sp') Q :=
  PyStmtTriple.assign fun env hP =>
    let ⟨v, hv, hQ⟩ := h env hP
    ⟨v, Env.set env x v, hv, rfl, hQ⟩

/-- `x op= e`: load the old value (which must not be a `list` — in-place
mutation is outside the v0 tier, `Semantics.lean`), evaluate `e`, apply the
operator (the pure `evalBinOp … = .ok r` hypothesis rules the error cases
out), fall through at `Env.set env x r`. -/
theorem PyStmtTriple.augAssign {m : Module} {P : Env → Prop} {Q : PyPost}
    {x : String} {op : BinOp} {e : Expr} {sp sp' : Span}
    (h : ∀ env, P env → ∃ old v r,
        Env.lookup env x = some old ∧ (∀ xs, old ≠ .list xs) ∧
        EvalsTo m env e v ∧ evalBinOp op old v = .ok r ∧
        Q.next (Env.set env x r)) :
    PyStmtTriple m P (.augAssign (.name x sp) op e sp') Q := by
  intro env hP
  obtain ⟨old, v, r, hlk, hnl, hv, hbin, hQ⟩ := h env hP
  obtain ⟨t, ht⟩ := hv.at_least
  refine ⟨t + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  cases old <;> first
    | exact absurd rfl (hnl _)
    | simpa [execStmt, hlk, ht F' hF', hbin] using hQ

/-- `if test: body else: orelse` — both-arm form: the test evaluates to a
value whose truthiness selects which branch precondition is guaranteed;
each branch runs under its own list triple into the same `Q`. -/
theorem PyStmtTriple.ifStmt {m : Module} {P Pt Pf : Env → Prop} {Q : PyPost}
    {test : Expr} {body orelse : Array Stmt} {sp : Span}
    (htest : ∀ env, P env → ∃ v, EvalsTo m env test v ∧
        (truthy v = true → Pt env) ∧ (truthy v = false → Pf env))
    (hbody : PyTriple m Pt body.toList Q)
    (horelse : PyTriple m Pf orelse.toList Q) :
    PyStmtTriple m P (.ifStmt test body orelse sp) Q := by
  intro env hP
  obtain ⟨v, hv, htrue, hfalse⟩ := htest env hP
  obtain ⟨t, ht⟩ := hv.at_least
  cases hb : truthy v
  · obtain ⟨r, tb, hr, hrun⟩ := horelse.exec (hfalse hb)
    refine ⟨t + tb + 1, fun F hF => ?_⟩
    obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
    simpa [execStmt, ht F' (by omega), hb, hrun F' (by omega)] using hr
  · obtain ⟨r, tb, hr, hrun⟩ := hbody.exec (htrue hb)
    refine ⟨t + tb + 1, fun F hF => ?_⟩
    obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
    simpa [execStmt, ht F' (by omega), hb, hrun F' (by omega)] using hr

/-! ## Smoke test

A hand-built three-statement straight-line program, proved through the
structural rules ONLY — no symbolic execution of the whole list; the leaf
`EvalsTo`/arm obligations close by `rfl` at the concrete environments. The
`#guard` pins the concrete run the triple asserts (non-vacuity). -/

section SmokeTest

private abbrev vcSp : Span := ⟨0, 0, 0, 0⟩
/-- `x = 3` -/
private abbrev vcS1 : Stmt := .assign #[.name "x" vcSp] (.constant (.int 3) vcSp) vcSp
/-- `y = x + 4` -/
private abbrev vcS2 : Stmt :=
  .assign #[.name "y" vcSp] (.binOp (.name "x" vcSp) .add (.constant (.int 4) vcSp) vcSp) vcSp
/-- `return x * y` -/
private abbrev vcS3 : Stmt :=
  .ret (some (.binOp (.name "x" vcSp) .mult (.name "y" vcSp) vcSp)) vcSp

#guard execStmts ⟨#[], #[]⟩ 32 [] [vcS1, vcS2, vcS3]
  == .ok ([("x", .int 3), ("y", .int 7)], .ret (.int 21))

/-- `x = 3; y = x + 4; return x * y` returns 21 — rules only, any module. -/
example (m : Module) :
    PyTriple m (fun env => env = []) [vcS1, vcS2, vcS3]
      (.ofRet fun v _ => v = .int 21) := by
  refine .seq (R := fun env => env = [("x", .int 3)]) (.assignName ?_)
    (.seq (R := fun env => env = [("x", .int 3), ("y", .int 7)]) (.assignName ?_)
      (.single (.ret ?_)))
  · rintro env rfl
    exact ⟨.int 3, .of_eval (fuel := 1) rfl, rfl⟩
  · rintro env rfl
    exact ⟨.int 7, .of_eval (fuel := 2) rfl, rfl⟩
  · rintro env rfl
    exact ⟨.int 21, .of_eval (fuel := 2) rfl, rfl⟩

end SmokeTest

end LeanModels.Python
