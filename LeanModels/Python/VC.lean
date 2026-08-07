import LeanModels.Python.Obs

/-!
# Flow-aware triples (`py_vcgen` layer 1: `PyPost` / `PyTriple`)

The v2 proof layer's foundation: a TOTAL-correctness Hoare triple over the
interpreter's statement level, with a *flow-aware* postcondition — since the
H1 core re-shape, over **frame states** (`FrameState`: the shared `World` +
this frame's locals) and the `Run`-typed interpreter.

Design (the settled forks, recorded):

* **`PyPost` mirrors `Std.Do`'s `PostCond`-with-shapes idea** specialized to
  our `RFlow`: one arm per way a statement list can land — `next` (fall
  through), `ret` (a `return` escaped), `brk`/`cont` (a loop-control flow
  escaped, consumed by an enclosing loop rule), plus an **`err` arm** that
  is STATE-AWARE (`PyErr → FrameState → Prop`, docs/memory-model.md v2):
  the interpreter retains state on `.exn`, so a raise-spec can observe the
  mutations and bindings made before the raise. Its default is
  `fun _ _ => False`, so straight-line specs never mention it.
  `Run.unsupported` gets NO arm: it lands in `False`, making a triple about
  an out-of-tier program unprovable — loud by construction. `.timeout` also
  lands in `False`: with the threshold quantifier below this is what makes
  the triple *total* correctness.

* **`PyTriple` is in fuel-threshold form** (`∃ t, ∀ F ≥ t, …`), not bare
  `∃ fuel` — the shape `fuelMono` composes: `PyTriple.exec` extracts a
  *decided outcome pinned at every larger fuel* (final state included —
  state is data), which is exactly what the `seq`/`ifStmt` proofs splice at
  whatever fuel the surrounding symbolic execution produces.

* **Pinned-state geometry (H1 stage 1).** Preconditions and invariants are
  predicates on whole frame states, and the walker (VCTactic.lean) keeps
  them in the shape `fun st => st = ⟨w, E⟩` with the world KNOWN — the
  geometry the h1-threading exploration validated (the VC walker needs a
  known mid-state; ∀-world triples hit parametricity walls at run splices).
  Stage-1 world invariance (`worldInv`, Obs.lean) is what keeps the world
  pinned across every splice.

* **Expression interface: `EvalsTo`** — the PURE-expression judgment: the
  evaluation decides with the state returned UNCHANGED
  (`evalExpr … st e = .ok st v`). Faithful in stage 1 (nothing allocates,
  `worldInv`; expressions never touch locals); replaced by stateful
  judgments when the dict tier lands. Same `∃ fuel` shape as `CallsTo`,
  same `at_least` threshold accessor.

Rule inventory: `PyTriple.nil`/`.seq`/`.single`/`.consequence`/`.frame`;
`PyStmtTriple.pass`/`.ret`/`.retNone`/`.brk`/`.cont`/`.exprStmt`/`.assign`
(generic `assignTo` target)/`.assignName`/`.augAssign`/`.ifStmt`/
`.consequence`. The `while` rule lives in VC2.lean
(`PyStmtTriple.whileLoop`, with the call rules, the `@[py_spec]` registry,
and the arrow⇄triple bridges), consuming the `brk`/`cont` arms this file
plumbs.
-/

namespace LeanModels.Python

/-! ## `PyPost` — the flow-aware postcondition -/

/-- Flow-aware postcondition of a statement list: one arm per landing.
`next` is the main arm (fall through, state transformed); `ret` sees the
returned value and the final state; `brk`/`cont` are consumed by an
enclosing loop rule; `err` (state-aware since H1 — the interpreter retains
state on `.exn`; default `False`) makes raise-specs stateable. `timeout`
and `unsupported` have no arms — see `PyPost.holds`. -/
structure PyPost where
  /-- The statements fell through normally (`RFlow.next`). -/
  next : FrameState → Prop
  /-- A `return` escaped with this value (`RFlow.ret`). -/
  ret : RVal → FrameState → Prop := fun _ _ => False
  /-- A `break` escaped (`RFlow.brk`) — consumed by an enclosing loop rule. -/
  brk : FrameState → Prop := fun _ => False
  /-- A `continue` escaped (`RFlow.cont`) — consumed by an enclosing loop rule. -/
  cont : FrameState → Prop := fun _ => False
  /-- The run raised this Python error (`Run.exn`), retaining this state
  (docs/memory-model.md v2: mutations before a raise survive). Default
  `False`: plain total-correctness specs assert error-freedom without
  mentioning it. -/
  err : PyErr → FrameState → Prop := fun _ _ => False

namespace PyPost

/-- Does an interpreter outcome land in the arm the postcondition
prescribes? `timeout` is `False` (the triple's threshold shape then
*excludes* it: total correctness); `unsupported` is `False` (out-of-tier
programs admit no triple — loud by construction, cf. `Obs.stuck` being
distinct from `diverges`). -/
def holds (Q : PyPost) : Run FrameState RFlow → Prop
  | .ok st .next => Q.next st
  | .ok st (.ret v) => Q.ret v st
  | .ok st .brk => Q.brk st
  | .ok st .cont => Q.cont st
  | .exn st e => Q.err e st
  | .timeout => False
  | .unsupported _ => False

@[simp] theorem holds_ok_next (Q : PyPost) (st : FrameState) :
    Q.holds (.ok st .next) = Q.next st := rfl
@[simp] theorem holds_ok_ret (Q : PyPost) (st : FrameState) (v : RVal) :
    Q.holds (.ok st (.ret v)) = Q.ret v st := rfl
@[simp] theorem holds_ok_brk (Q : PyPost) (st : FrameState) :
    Q.holds (.ok st .brk) = Q.brk st := rfl
@[simp] theorem holds_ok_cont (Q : PyPost) (st : FrameState) :
    Q.holds (.ok st .cont) = Q.cont st := rfl
@[simp] theorem holds_exn (Q : PyPost) (st : FrameState) (e : PyErr) :
    Q.holds (.exn st e) = Q.err e st := rfl
@[simp] theorem holds_timeout (Q : PyPost) :
    Q.holds .timeout = False := rfl
@[simp] theorem holds_unsupported (Q : PyPost) (msg : String) :
    Q.holds (.unsupported msg) = False := rfl

/-- An outcome landing in an arm is decided — the hook that lets `fuelMono`
pin it at every larger fuel (`PyTriple.exec`). -/
theorem holds_ne_timeout {Q : PyPost} {r : Run FrameState RFlow}
    (h : Q.holds r) : r ≠ .timeout := fun ht => by subst ht; exact h

/-- Postcondition of code that falls through normally into `Q` — every other
arm `False` (straight-line statement lists between control constructs). -/
def ofNext (Q : FrameState → Prop) : PyPost := { next := Q }

/-- Postcondition of code that always `return`s into `Q` — every other arm
`False` (the function-body shape the `CallsTo` bridge consumes). -/
def ofRet (Q : RVal → FrameState → Prop) : PyPost :=
  { next := fun _ => False, ret := Q }

/-- Arm-wise entailment `Q → Q'` — the postcondition side of
`PyTriple.consequence`. -/
structure Entails (Q Q' : PyPost) : Prop where
  next : ∀ st, Q.next st → Q'.next st
  ret : ∀ v st, Q.ret v st → Q'.ret v st
  brk : ∀ st, Q.brk st → Q'.brk st
  cont : ∀ st, Q.cont st → Q'.cont st
  err : ∀ e st, Q.err e st → Q'.err e st

theorem Entails.rfl (Q : PyPost) : Entails Q Q :=
  ⟨fun _ h => h, fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ _ h => h⟩

/-- Entailment transports `holds` — outcome-shape-agnostic weakening. -/
theorem Entails.holds {Q Q' : PyPost} (h : Entails Q Q') :
    ∀ {r : Run FrameState RFlow}, Q.holds r → Q'.holds r
  | .ok st .next, hr => h.next st hr
  | .ok st (.ret v), hr => h.ret v st hr
  | .ok st .brk, hr => h.brk st hr
  | .ok st .cont, hr => h.cont st hr
  | .exn st e, hr => h.err e st hr
  | .timeout, hr => hr.elim
  | .unsupported _, hr => hr.elim

/-- Conjoin a pure (state-independent) proposition onto every arm —
the postcondition side of `PyTriple.frame`. -/
def and (Q : PyPost) (R : Prop) : PyPost where
  next st := Q.next st ∧ R
  ret v st := Q.ret v st ∧ R
  brk st := Q.brk st ∧ R
  cont st := Q.cont st ∧ R
  err e st := Q.err e st ∧ R

theorem holds_and {Q : PyPost} {R : Prop} {r : Run FrameState RFlow}
    (h : Q.holds r) (hR : R) : (Q.and R).holds r := by
  match r with
  | .ok st .next | .ok st (.ret v) | .ok st .brk | .ok st .cont
  | .exn st e => exact ⟨h, hR⟩
  | .timeout | .unsupported _ => exact h.elim

end PyPost

/-! ## The expression-evaluation interface -/

/-- Terminating PURE expression evaluation: *some* fuel evaluates `e` to
`v` in `st` with the state returned unchanged — the expression-level
`CallsTo` (same `∃ fuel` shape, same `at_least` threshold accessor).
Pinned-state (H1 stage 1): the out-state IS the in-state, which is what
lets the walker keep a known mid-state through a splice; nested calls
inside `e` preserve the world by `worldInv`, and expressions never touch
locals. Discharge at a concrete state with `EvalsTo.of_eval` + `rfl` (or
`py_simp`), at a symbolic one by whatever computes the evaluation. -/
def EvalsTo (m : Module) (st : FrameState) (e : Expr) (v : RVal) : Prop :=
  ∃ fuel, evalExpr m fuel st e = .ok st v

/-- Introduce `EvalsTo` from one concrete run (any fuel — monotonicity is
`at_least`'s job, not the introduction's). -/
theorem EvalsTo.of_eval {m : Module} {fuel : Nat} {st : FrameState} {e : Expr}
    {v : RVal} (h : evalExpr m fuel st e = .ok st v) : EvalsTo m st e v :=
  ⟨fuel, h⟩

/-- Fuel-threshold form of an `EvalsTo` fact (the `CallsTo.at_least` analog):
the evaluation succeeds at *every* sufficiently large fuel. Every rule below
consumes its expression hypotheses through this. -/
theorem EvalsTo.at_least {m : Module} {st : FrameState} {e : Expr} {v : RVal}
    (h : EvalsTo m st e v) :
    ∃ t, ∀ F ≥ t, evalExpr m F st e = .ok st v := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, fun F hF => evalExpr_mono hf (by simp) F hF⟩

/-! ## The triples -/

/-- Statement-level total-correctness triple: from any frame state
satisfying `P`, some fuel threshold `t` makes `execStmt` land in the arm
`Q` prescribes at *every* fuel `F ≥ t` (timeout is thereby excluded — total
correctness; `unsupported` is excluded because no arm accepts it). The
per-statement structural rules conclude this; `PyTriple.seq` consumes it. -/
def PyStmtTriple (m : Module) (P : FrameState → Prop) (s : Stmt) (Q : PyPost) : Prop :=
  ∀ st, P st → ∃ t, ∀ F ≥ t, Q.holds (execStmt m F st s)

/-- **The triple of the py_vcgen layer**: total correctness of a statement
list, threshold form (see `PyStmtTriple`; same shape one level up, over
`execStmts`). The threshold quantifier is what makes triples compose by
`fuelMono`: `PyTriple.exec` extracts a single decided outcome valid at
every larger fuel, spliceable wherever the surrounding execution lands. -/
def PyTriple (m : Module) (P : FrameState → Prop) (ss : List Stmt) (Q : PyPost) : Prop :=
  ∀ st, P st → ∃ t, ∀ F ≥ t, Q.holds (execStmts m F st ss)

/-- Destructure a nonzero-threshold bound: `F ≥ t + 1` is a successor
`F' + 1` with `F' ≥ t` — the one-step unfold shape every rule proof uses
(the interpreter matches fuel first). -/
private theorem succ_le_dest {t F : Nat} (h : t + 1 ≤ F) :
    ∃ F', F = F' + 1 ∧ t ≤ F' := ⟨F - 1, by omega, by omega⟩

/-- Extraction (the composability engine): a statement triple yields, per
`P`-state, one *decided* outcome in `Q`'s arm together with a threshold
pinning `execStmt` to it at every larger fuel — `holds_ne_timeout` +
`execStmt_mono` (FuelMono). Rules splice this at whatever fuel their own
symbolic execution produces, side conditions by `omega`. -/
theorem PyStmtTriple.exec {m : Module} {P : FrameState → Prop} {s : Stmt}
    {Q : PyPost} (h : PyStmtTriple m P s Q) {st : FrameState} (hP : P st) :
    ∃ r t, Q.holds r ∧ ∀ F ≥ t, execStmt m F st s = r := by
  obtain ⟨t, ht⟩ := h st hP
  have h0 := ht t (Nat.le_refl t)
  exact ⟨_, t, h0, execStmt_mono rfl (PyPost.holds_ne_timeout h0)⟩

/-- Extraction at the list level — see `PyStmtTriple.exec`. -/
theorem PyTriple.exec {m : Module} {P : FrameState → Prop} {ss : List Stmt}
    {Q : PyPost} (h : PyTriple m P ss Q) {st : FrameState} (hP : P st) :
    ∃ r t, Q.holds r ∧ ∀ F ≥ t, execStmts m F st ss = r := by
  obtain ⟨t, ht⟩ := h st hP
  have h0 := ht t (Nat.le_refl t)
  exact ⟨_, t, h0, execStmts_mono rfl (PyPost.holds_ne_timeout h0)⟩

/-- Introduction from a single-fuel witness per state: one decided run
in the right arm suffices — `execStmt_mono` supplies the threshold. -/
theorem PyStmtTriple.of_exec {m : Module} {P : FrameState → Prop} {s : Stmt}
    {Q : PyPost} (h : ∀ st, P st → ∃ fuel, Q.holds (execStmt m fuel st s)) :
    PyStmtTriple m P s Q := by
  intro st hP
  obtain ⟨fuel, hf⟩ := h st hP
  refine ⟨fuel, fun F hF => ?_⟩
  rw [execStmt_mono rfl (PyPost.holds_ne_timeout hf) F hF]
  exact hf

/-- Introduction from a single-fuel witness — see `PyStmtTriple.of_exec`. -/
theorem PyTriple.of_exec {m : Module} {P : FrameState → Prop} {ss : List Stmt}
    {Q : PyPost} (h : ∀ st, P st → ∃ fuel, Q.holds (execStmts m fuel st ss)) :
    PyTriple m P ss Q := by
  intro st hP
  obtain ⟨fuel, hf⟩ := h st hP
  refine ⟨fuel, fun F hF => ?_⟩
  rw [execStmts_mono rfl (PyPost.holds_ne_timeout hf) F hF]
  exact hf

/-! ## Structural rules — list level -/

/-- Empty list: falls through with the state untouched, so the `next` arm
must hold outright (the Hoare `skip`). -/
theorem PyTriple.nil {m : Module} {P : FrameState → Prop} {Q : PyPost}
    (h : ∀ st, P st → Q.next st) : PyTriple m P [] Q := by
  intro st hP
  refine ⟨1, fun F hF => ?_⟩
  obtain ⟨F', rfl, -⟩ := succ_le_dest hF
  simpa [execStmts] using h st hP

/-- **Sequencing** — the composition rule and the only place flow routing
lives: run `s` under a postcondition whose `next` arm is the midcondition
`R`, then the rest from `R`; every non-`next` arm of `Q` passes through `s`
directly, bypassing `rest`, exactly as `execStmts` short-circuits (mirror of
`Std.Do`'s bind-spec threading its exception conditions unchanged).
Thresholds compose by splicing the two extracted runs at a summed bound —
`fuelMono` under the hood, `omega` for the arithmetic. -/
theorem PyTriple.seq {m : Module} {P R : FrameState → Prop} {Q : PyPost}
    {s : Stmt} {rest : List Stmt}
    (h1 : PyStmtTriple m P s { Q with next := R })
    (h2 : PyTriple m R rest Q) : PyTriple m P (s :: rest) Q := by
  intro st hP
  obtain ⟨r1, t1, hr1, hstep1⟩ := h1.exec hP
  cases r1 with
  | ok st' flow =>
    cases flow with
    | next =>
      obtain ⟨r2, t2, hr2, hstep2⟩ := h2.exec (show R st' from hr1)
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
  | exn st' e =>
    refine ⟨t1 + 1, fun F hF => ?_⟩
    obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
    simpa [execStmts, hstep1 F' hF'] using hr1
  | timeout => exact (PyPost.holds_ne_timeout hr1 rfl).elim
  | unsupported msg => exact hr1.elim

/-- Singleton list from a statement triple (`seq` against `nil`; the
midcondition is `Q.next` itself, closed by structure eta). -/
theorem PyTriple.single {m : Module} {P : FrameState → Prop} {s : Stmt}
    {Q : PyPost} (h : PyStmtTriple m P s Q) : PyTriple m P [s] Q :=
  PyTriple.seq (R := Q.next) h (PyTriple.nil fun _ hQ => hQ)

/-- Consequence: strengthen the precondition, weaken every arm. -/
theorem PyTriple.consequence {m : Module} {P P' : FrameState → Prop}
    {ss : List Stmt} {Q Q' : PyPost} (h : PyTriple m P ss Q)
    (hpre : ∀ st, P' st → P st) (hpost : Q.Entails Q') :
    PyTriple m P' ss Q' := by
  intro st hP
  obtain ⟨t, ht⟩ := h st (hpre st hP)
  exact ⟨t, fun F hF => hpost.holds (ht F hF)⟩

/-- Consequence at the statement level — see `PyTriple.consequence`. -/
theorem PyStmtTriple.consequence {m : Module} {P P' : FrameState → Prop}
    {s : Stmt} {Q Q' : PyPost} (h : PyStmtTriple m P s Q)
    (hpre : ∀ st, P' st → P st) (hpost : Q.Entails Q') :
    PyStmtTriple m P' s Q' := by
  intro st hP
  obtain ⟨t, ht⟩ := h st (hpre st hP)
  exact ⟨t, fun F hF => hpost.holds (ht F hF)⟩

/-- Frame a *pure* proposition through a triple: `R` rides along into every
arm. Only state-independent framing is offered — statements mutate the
state, so a state-dependent frame would be unsound in general (a
separation-logic-style footprint discipline is a later phase's concern). -/
theorem PyTriple.frame {m : Module} {P : FrameState → Prop} {ss : List Stmt}
    {Q : PyPost} (R : Prop) (h : PyTriple m P ss Q) :
    PyTriple m (fun st => P st ∧ R) ss (Q.and R) := by
  intro st hPR
  obtain ⟨t, ht⟩ := h st hPR.1
  exact ⟨t, fun F hF => PyPost.holds_and (ht F hF) hPR.2⟩

/-! ## Structural rules — statement level

Each rule is proved against the interpreter by one-step symbolic execution:
destructure the threshold bound to expose a successor fuel (`succ_le_dest`),
unfold `execStmt` at it, splice the expression runs (threshold form,
`omega` side conditions), and land in the prescribed arm. Hypotheses are in
wp shape — `∀ st, P st → ∃ …value…, EvalsTo … ∧ <arm at the new state>` —
so a vcgen tactic can compute them outside-in. -/

/-- `pass`: falls through, state untouched. -/
theorem PyStmtTriple.pass {m : Module} {P : FrameState → Prop} {Q : PyPost}
    {sp : Span} (h : ∀ st, P st → Q.next st) : PyStmtTriple m P (.pass sp) Q := by
  intro st hP
  refine ⟨1, fun F hF => ?_⟩
  obtain ⟨F', rfl, -⟩ := succ_le_dest hF
  simpa [execStmt] using h st hP

/-- `break`: discharges into the `brk` arm. -/
theorem PyStmtTriple.brk {m : Module} {P : FrameState → Prop} {Q : PyPost}
    {sp : Span} (h : ∀ st, P st → Q.brk st) : PyStmtTriple m P (.brk sp) Q := by
  intro st hP
  refine ⟨1, fun F hF => ?_⟩
  obtain ⟨F', rfl, -⟩ := succ_le_dest hF
  simpa [execStmt] using h st hP

/-- `continue`: discharges into the `cont` arm. -/
theorem PyStmtTriple.cont {m : Module} {P : FrameState → Prop} {Q : PyPost}
    {sp : Span} (h : ∀ st, P st → Q.cont st) : PyStmtTriple m P (.cont sp) Q := by
  intro st hP
  refine ⟨1, fun F hF => ?_⟩
  obtain ⟨F', rfl, -⟩ := succ_le_dest hF
  simpa [execStmt] using h st hP

/-- Bare `return`: discharges into the `ret` arm at `RVal.none`. -/
theorem PyStmtTriple.retNone {m : Module} {P : FrameState → Prop} {Q : PyPost}
    {sp : Span} (h : ∀ st, P st → Q.ret .none st) :
    PyStmtTriple m P (.ret Option.none sp) Q := by
  intro st hP
  refine ⟨1, fun F hF => ?_⟩
  obtain ⟨F', rfl, -⟩ := succ_le_dest hF
  simpa [execStmt] using h st hP

/-- `return e`: evaluate `e`, discharge into the `ret` arm at its value. -/
theorem PyStmtTriple.ret {m : Module} {P : FrameState → Prop} {Q : PyPost}
    {e : Expr} {sp : Span}
    (h : ∀ st, P st → ∃ v, EvalsTo m st e v ∧ Q.ret v st) :
    PyStmtTriple m P (.ret (some e) sp) Q := by
  intro st hP
  obtain ⟨v, hv, hQ⟩ := h st hP
  obtain ⟨t, ht⟩ := hv.at_least
  refine ⟨t + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  simpa [execStmt, ht F' hF'] using hQ

/-- Expression statement: evaluate (pure in stage 1 — `EvalsTo` pins the
state), fall through with the state untouched. -/
theorem PyStmtTriple.exprStmt {m : Module} {P : FrameState → Prop} {Q : PyPost}
    {e : Expr} {sp : Span}
    (h : ∀ st, P st → ∃ v, EvalsTo m st e v ∧ Q.next st) :
    PyStmtTriple m P (.exprStmt e sp) Q := by
  intro st hP
  obtain ⟨v, hv, hQ⟩ := h st hP
  obtain ⟨t, ht⟩ := hv.at_least
  refine ⟨t + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  simpa [execStmt, ht F' hF'] using hQ

/-- Single-target assignment, generic over the target: evaluate the value,
store it with the pure helper `assignTo` (which handles both `Name` and
tuple-unpacking targets — the `assignTo … = .ok env'` hypothesis is
discharged by `rfl`/`py_simp` at concrete targets), fall through at the
updated locals (the world rides unchanged). -/
theorem PyStmtTriple.assign {m : Module} {P : FrameState → Prop} {Q : PyPost}
    {tgt e : Expr} {sp : Span}
    (h : ∀ st, P st → ∃ v env', EvalsTo m st e v ∧
        assignTo st.locals tgt v = .ok env' ∧ Q.next ⟨st.world, env'⟩) :
    PyStmtTriple m P (.assign #[tgt] e sp) Q := by
  intro st hP
  obtain ⟨v, env', hv, ha, hQ⟩ := h st hP
  obtain ⟨t, ht⟩ := hv.at_least
  refine ⟨t + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  -- subscript targets never satisfy the pure `assignTo` hypothesis (loud
  -- arm), so that case closes by contradiction; every other target
  -- reduces as before (H2: the interpreter runs `assignToH`, which agrees
  -- with a decided pure `assignTo` — `assignToH_of_assignTo`)
  cases tgt <;>
    first
    | simpa [execStmt, ht F' hF', assignToH_of_assignTo ha] using hQ
    | simp [assignTo] at ha

/-- `x = e` (the `Name`-target special case, `assignTo` pre-reduced): fall
through at `Env.set st.locals x v`. -/
theorem PyStmtTriple.assignName {m : Module} {P : FrameState → Prop}
    {Q : PyPost} {x : String} {e : Expr} {sp sp' : Span}
    (h : ∀ st, P st → ∃ v, EvalsTo m st e v ∧
        Q.next ⟨st.world, Env.set st.locals x v⟩) :
    PyStmtTriple m P (.assign #[.name x sp] e sp') Q :=
  PyStmtTriple.assign fun st hP =>
    let ⟨v, hv, hQ⟩ := h st hP
    ⟨v, Env.set st.locals x v, hv, rfl, hQ⟩

/-- `x op= e`: load the old value (which must be neither a `listV` — in-place
mutation is outside the v0 tier — nor a heap `.ref`, outside the stage-1
tier), evaluate `e`, apply the operator (the pure `evalBinOp … = .ok r`
hypothesis rules the error cases out), fall through at
`Env.set st.locals x r`. -/
theorem PyStmtTriple.augAssign {m : Module} {P : FrameState → Prop}
    {Q : PyPost} {x : String} {op : BinOp} {e : Expr} {sp sp' : Span}
    (h : ∀ st, P st → ∃ old v r,
        Env.lookup st.locals x = some old ∧ (∀ xs, old ≠ .listV xs) ∧
        (∀ a, old ≠ .ref a) ∧
        EvalsTo m st e v ∧ evalBinOp op old v = .ok r ∧
        Q.next ⟨st.world, Env.set st.locals x r⟩) :
    PyStmtTriple m P (.augAssign (.name x sp) op e sp') Q := by
  intro st hP
  obtain ⟨old, v, r, hlk, hnl, hnr, hv, hbin, hQ⟩ := h st hP
  obtain ⟨t, ht⟩ := hv.at_least
  refine ⟨t + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  cases old <;> first
    | exact absurd rfl (hnl _)
    | exact absurd rfl (hnr _)
    | simpa [execStmt, hlk, ht F' hF', hbin] using hQ

/-- `if test: body else: orelse` — both-arm form: the test evaluates to a
value whose truthiness (a `Res`-valued DECISION since H1 — the hypothesis
also proves the test value is not a loud `.ref`) selects which branch
precondition is guaranteed; each branch runs under its own list triple
into the same `Q`. -/
theorem PyStmtTriple.ifStmt {m : Module} {P Pt Pf : FrameState → Prop}
    {Q : PyPost} {test : Expr} {body orelse : Array Stmt} {sp : Span}
    (htest : ∀ st, P st → ∃ v b, EvalsTo m st test v ∧ truthy v = .ok b ∧
        (b = true → Pt st) ∧ (b = false → Pf st))
    (hbody : PyTriple m Pt body.toList Q)
    (horelse : PyTriple m Pf orelse.toList Q) :
    PyStmtTriple m P (.ifStmt test body orelse sp) Q := by
  intro st hP
  obtain ⟨v, b, hv, htr, htrue, hfalse⟩ := htest st hP
  obtain ⟨t, ht⟩ := hv.at_least
  cases b
  · obtain ⟨r, tb, hr, hrun⟩ := horelse.exec (hfalse rfl)
    refine ⟨t + tb + 1, fun F hF => ?_⟩
    obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
    simpa [execStmt, ht F' (by omega), truthyH_of_truthy htr, hrun F' (by omega)] using hr
  · obtain ⟨r, tb, hr, hrun⟩ := hbody.exec (htrue rfl)
    refine ⟨t + tb + 1, fun F hF => ?_⟩
    obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
    simpa [execStmt, ht F' (by omega), truthyH_of_truthy htr, hrun F' (by omega)] using hr

/-! ## Smoke test

A hand-built three-statement straight-line program, proved through the
structural rules ONLY — no symbolic execution of the whole list; the leaf
`EvalsTo`/arm obligations close by `rfl` at the concrete states (state
threading is definitional in stage 1: nothing moves the world). The
`#guard` pins the concrete run the triple asserts (non-vacuity). -/

section SmokeTest

private abbrev vcSp : Span := ⟨0, 0, 0, 0⟩
private abbrev vcW : World := ⟨#[], [], []⟩
/-- `x = 3` -/
private abbrev vcS1 : Stmt := .assign #[.name "x" vcSp] (.constant (.int 3) vcSp) vcSp
/-- `y = x + 4` -/
private abbrev vcS2 : Stmt :=
  .assign #[.name "y" vcSp] (.binOp (.name "x" vcSp) .add (.constant (.int 4) vcSp) vcSp) vcSp
/-- `return x * y` -/
private abbrev vcS3 : Stmt :=
  .ret (some (.binOp (.name "x" vcSp) .mult (.name "y" vcSp) vcSp)) vcSp

#guard execStmts ⟨#[], #[]⟩ 32 ⟨vcW, []⟩ [vcS1, vcS2, vcS3]
  == .ok ⟨vcW, [("x", .int 3), ("y", .int 7)]⟩ (.ret (.int 21))

/-- `x = 3; y = x + 4; return x * y` returns 21 — rules only, any module. -/
example (m : Module) :
    PyTriple m (fun st => st = ⟨vcW, []⟩) [vcS1, vcS2, vcS3]
      (.ofRet fun v _ => v = .int 21) := by
  refine .seq (R := fun st => st = ⟨vcW, [("x", .int 3)]⟩) (.assignName ?_)
    (.seq (R := fun st => st = ⟨vcW, [("x", .int 3), ("y", .int 7)]⟩)
      (.assignName ?_)
      (.single (.ret ?_)))
  · rintro st rfl
    exact ⟨.int 3, .of_eval (fuel := 1) rfl, rfl⟩
  · rintro st rfl
    exact ⟨.int 7, .of_eval (fuel := 2) rfl, rfl⟩
  · rintro st rfl
    exact ⟨.int 21, .of_eval (fuel := 2) rfl, rfl⟩

end SmokeTest

end LeanModels.Python
