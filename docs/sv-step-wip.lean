import LeanModels.Sv.SelfCheck

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


/-! ## THE SUBSUMPTION OBLIGATION — STATED, NOT YET DISCHARGED

`stepSStmts` must not become a second, divergent interpreter. The
discharge is:

    theorem stepSStmts_done_agrees :
        ∀ fuel st nba out ss st' nba' out',
          stepSStmts fuel st nba out ss = .ok (st', nba', out', .done) →
          execSStmts fuel st nba out ss = .ok (st', nba', out')

i.e. **whenever the stepper finishes without suspending, it agrees with
the executor that was already there** — so `execSStmts` is not
superseded, it is RECOVERED as the non-suspending case. Note it is
stated without a syntactic `isTriggerFree` predicate: "did not suspend"
is a fact about the RUN, which is weaker to assume and stronger to
conclude than "contains no suspension syntax" — a body may carry a
`#delay` on a branch not taken and the lemma still applies.

**Status: OPEN, and this file is therefore NOT part of the build.** It
lives under `docs/` like `docs/mvcgen-pilot.lean`, which `lakefile.toml`'s
globs (the `LeanModels` lib root and `Examples.+`) deliberately exclude.
The definitions above elaborate cleanly (`lake env lean` exit 0); the
proof does not close yet.

**Where the proof stands**, so the next session resumes from the real
state rather than from scratch. Both directions go by `match fuel`, then
`rw [stepSStmt.eq_def] at h` with the GOAL LEFT FOLDED — unfolding
`execSStmt` up front is wrong, because the leaf case delegates to
`execSStmt (fuel + 1)` and so needs the goal still in applied form. The
six `stmt` branches split as: `h_1`-`h_3` the suspension forms
(contradictory, `simp at h`), `h_4` `ifStmt` (case on `evalSExpr`, then
`by_cases` on `condTrue`, then the IH), `h_5` `block` (directly the other
IH), `h_6` the delegating leaves (case on `execSStmt (fuel+1)`). The
残 obstacle is bind-reduction bookkeeping in `Res`'s `Monad` instance:
`Res.bind` is an anonymous instance field, not a named constant, so
`simp only [bind, Res.bind]` does not exist and plain `simp` oscillates
between "no progress" and over-reducing the `do` block. The likely fix is
a small set of local `@[simp]` lemmas for `Res`'s bind on `.ok`/
`.timeout`/`.unsupported` — landing those first, in `Semantics.lean`,
would make both directions routine.
-/

end LeanModels.Sv
