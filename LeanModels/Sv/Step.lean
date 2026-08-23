import LeanModels.Sv.SelfCheck
-- Obs.lean carries the `Res` do-notation stepping rules as GLOBAL simp
-- lemmas (`pure_eq`, `ok_bind`, `timeout_bind`, `unsupported_bind`,
-- `bind_eq_ok`), mirroring the Python lane's set. They are the whole reason
-- the subsumption proof below reduces: without this import they are out of
-- scope, `simp` cannot step a `do` block over `Res`, and it oscillates
-- between "no progress" and over-reducing. SelfCheck does not import Obs,
-- so this line is load-bearing rather than incidental.
import LeanModels.Sv.Obs

/-!
# R1 inch 4a, step 2 — the RESUMABLE stepper

`execSStmt`/`execSStmts` run a process body to completion. IEEE 1800
processes do not: they pause mid-body at `#`, `@` and `wait`, other
processes run, and they resume where they stopped (clause 4; see
`docs/sv-r1-scheduler.md` §9.3).

`SemM` cannot express that as an effect — `ExceptT ρ (StateT W Halt) α`
unfolds to `W → (Except ρ α × W)`, which has an `α`, a `ρ` and a `W` and
**no third case**. So suspension is DEFUNCTIONALIZED: the continuation is
DATA — the remaining statement list — and the step function returns it.
This is sound because SV's suspension points are SYNTACTIC, so "where it
paused" is a position in the program text rather than an arbitrary
closure.

## What this file is, and is not

It is the process-local half: *run one body until it finishes or pauses*.
It is **not** the scheduler — there is no process table, no time wheel and
no region loop here; those are `SvWorld` and come next.

## The subsumption obligation

`stepSStmts` must not be a second, divergent interpreter. `execSStmts` is
recovered as its non-suspending case, and `stepSStmts_done_agrees` is the
proof — the adequacy-shaped lemma of §9.3, discharged here rather than
asserted. Every constructor that cannot contain a nested statement
DELEGATES to `execSStmt`, so the two cannot drift on those cases by
construction; only `ifStmt`, `block` and the three suspension forms are
written twice, and the lemma covers them.
-/

namespace LeanModels.Sv

open SelfCheck

-- `Edge`/`SStmt`/`Out`/`execSStmt`/`evalSExpr` live in `LeanModels.Sv.SelfCheck`.
-- Without this, a mistyped or unopened name is silently auto-bound as an
-- implicit universe variable rather than reported: the first draft of this
-- file turned `Edge` into `Sort ?u`. Fail loudly instead.
set_option autoImplicit false

/-- Why a process paused. The scheduler resumes it when the trigger fires. -/
inductive Trigger where
  /-- `#d` — resume after `amount` time units. -/
  | atTime (amount : Nat)
  /-- `@(posedge sig)` etc. — resume on the named edge of `sig`. -/
  | atEdge (sig : String) (edge : Edge)
  /-- `wait (cond)` — resume when `cond` becomes true. -/
  | onCond (cond : SExpr)
deriving Repr, Inhabited

/-- The result of stepping a process body once.

`suspended` carries the DEFUNCTIONALIZED CONTINUATION: the statements that
still have to run when the trigger fires. -/
inductive StepOutcome where
  | done
  | suspended (trigger : Trigger) (residual : List SStmt)
deriving Repr, Inhabited

mutual

/-- Step one statement: run it to completion, or to its first suspension
point. Constructors that cannot contain a nested statement delegate to
`execSStmt`, which is what keeps the two interpreters from drifting. -/
def stepSStmt (fuel : Nat) (st : SvState) (nba : NbaQueue) (out : Out)
    (stmt : SStmt) : Res (SvState × NbaQueue × Out × StepOutcome) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    if out.halted then .ok (st, nba, out, .done)
    else
      match stmt with
      -- Suspension: stop here, with nothing of THIS statement left to do.
      | .delay amount => .ok (st, nba, out, .suspended (.atTime amount) [])
      | .waitEvent sig edge => .ok (st, nba, out, .suspended (.atEdge sig edge) [])
      | .waitCond cond => .ok (st, nba, out, .suspended (.onCond cond) [])
      -- Compound: recurse, because a nested statement may suspend.
      | .ifStmt cond thenB elseB => do
          let c ← evalSExpr fuel st cond
          if c.condTrue then
            stepSStmt fuel st nba out thenB
          else
            match elseB with
            | some s => stepSStmt fuel st nba out s
            | none => .ok (st, nba, out, .done)
      | .block body => stepSStmts fuel st nba out body.toList
      -- Leaves: delegate, so they cannot drift from `execSStmt`.
      | s => do
          let (st', nba', out') ← execSStmt (fuel + 1) st nba out s
          return (st', nba', out', .done)

/-- Step a statement list. On suspension the residual is the rest of THIS
statement's work followed by the statements not yet reached — which is the
process's continuation. -/
def stepSStmts (fuel : Nat) (st : SvState) (nba : NbaQueue) (out : Out)
    (ss : List SStmt) : Res (SvState × NbaQueue × Out × StepOutcome) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match ss with
    | [] => .ok (st, nba, out, .done)
    | s :: rest => do
        let (st', nba', out', oc) ← stepSStmt fuel st nba out s
        match oc with
        | .done => stepSStmts fuel st' nba' out' rest
        | .suspended t residual =>
            .ok (st', nba', out', .suspended t (residual ++ rest))

end


/-! ## THE SUBSUMPTION OBLIGATION

**Whenever the stepper finishes without suspending, it agrees with the
executor that was already there** — so `execSStmts` is not superseded, it
is RECOVERED as the non-suspending case, and `stepSStmts` cannot drift
into a second interpreter.

Stated WITHOUT a syntactic `isTriggerFree` predicate: "did not suspend" is
a fact about the RUN, weaker to assume and stronger to conclude than
"contains no suspension syntax" — a body may carry a `#delay` on a branch
that was not taken and the lemma still applies to it.

**The goal is left FOLDED** in the first theorem: the delegating-leaf case
calls `execSStmt (fuel + 1)`, so unfolding `execSStmt` up front puts the
goal in a shape that case cannot discharge. Each branch unfolds it
locally instead. -/

mutual

theorem stepSStmt_done_agrees : ∀ (fuel : Nat) (st : SvState) (nba : NbaQueue)
    (out : Out) (stmt : SStmt) (st' : SvState) (nba' : NbaQueue) (out' : Out),
    stepSStmt fuel st nba out stmt = .ok (st', nba', out', .done) →
    execSStmt fuel st nba out stmt = .ok (st', nba', out') := by
  intro fuel
  match fuel with
  | 0 => intro st nba out stmt st' nba' out' h; simp [stepSStmt] at h
  | fuel + 1 =>
    intro st nba out stmt st' nba' out' h
    rw [stepSStmt.eq_def] at h
    simp only at h
    split at h
    · next hh =>
      rw [SelfCheck.execSStmt.eq_def]; simp only [hh, if_true]; simp_all
    · next hh =>
      split at h
      case h_1 | h_2 | h_3 => simp at h
      case h_4 cond thenB elseB =>
        rw [SelfCheck.execSStmt.eq_def]; simp only [hh]
        cases hc : evalSExpr fuel st cond with
        | ok c =>
          simp only [hc, Res.ok_bind] at h ⊢
          by_cases hct : c.condTrue = true
          · simp only [hct, if_true] at h ⊢
            exact stepSStmt_done_agrees fuel _ _ _ _ _ _ _ h
          · simp only [hct] at h ⊢
            cases elseB with
            | none => simp_all
            | some sE => exact stepSStmt_done_agrees fuel _ _ _ _ _ _ _ h
        | timeout => simp only [hc, Res.timeout_bind] at h; simp at h
        | unsupported m => simp only [hc, Res.unsupported_bind] at h; simp at h
      case h_5 body =>
        rw [SelfCheck.execSStmt.eq_def]; simp only [hh]
        exact stepSStmts_done_agrees fuel _ _ _ _ _ _ _ h
      case h_6 =>
        cases he : execSStmt (fuel + 1) st nba out stmt with
        | ok r =>
          obtain ⟨ra, rb, rc⟩ := r
          simp only [he, Res.ok_bind, Res.pure_eq] at h ⊢
          simp_all
        | timeout => simp only [he, Res.timeout_bind] at h; simp at h
        | unsupported m => simp only [he, Res.unsupported_bind] at h; simp at h

theorem stepSStmts_done_agrees : ∀ (fuel : Nat) (st : SvState) (nba : NbaQueue)
    (out : Out) (ss : List SStmt) (st' : SvState) (nba' : NbaQueue) (out' : Out),
    stepSStmts fuel st nba out ss = .ok (st', nba', out', .done) →
    execSStmts fuel st nba out ss = .ok (st', nba', out') := by
  intro fuel
  match fuel with
  | 0 => intro st nba out ss st' nba' out' h; simp [stepSStmts] at h
  | fuel + 1 =>
    intro st nba out ss st' nba' out' h
    rw [stepSStmts.eq_def] at h
    rw [SelfCheck.execSStmts.eq_def]
    simp only at h ⊢
    cases ss with
    | nil => simp_all
    | cons sHd rest =>
      simp only at h ⊢
      cases hs : stepSStmt fuel st nba out sHd with
      | ok r =>
        obtain ⟨sa, nb, ou, oc⟩ := r
        simp only [hs, Res.ok_bind] at h
        cases oc with
        | done =>
          have hx := stepSStmt_done_agrees fuel st nba out sHd sa nb ou hs
          simp only [hx, Res.ok_bind]
          exact stepSStmts_done_agrees fuel _ _ _ _ _ _ _ h
        | suspended t r => simp at h
      | timeout => simp only [hs, Res.timeout_bind] at h; simp at h
      | unsupported m => simp only [hs, Res.unsupported_bind] at h; simp at h

end

end LeanModels.Sv
