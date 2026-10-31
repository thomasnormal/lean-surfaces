import LeanModels.Sv.Load

namespace Examples.systemVerilog.foreverLoops.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- Exact source subtrees, checked against the loaded envelopes below.
def trueCondition : SExpr := .m0 (.lit (.ofNat 1 1))
def eventBody : SStmt := .waitEvent "trigger" .pos
def eventLoop : SStmt := .forLoop #[] trueCondition #[] eventBody
def breakBody : SStmt := .block #[.delay 2, .breakLoop]
def timedLoop : SStmt := .forLoop #[] trueCondition #[] breakBody

private theorem true_test : (LVec.ofNat 1 1).condTrue = true := by
  simp only [LVec.condTrue, LVec.ofNat, ← Array.any_toList]
  simp [Array.toList_ofFn, List.ofFn_succ]

/-- The event body leaves the complete frame and its loop boundary retained. -/
theorem event_retains (state : SvState) (pending : NbaQueue) (output : Out)
    (fuel : Nat) (running : output.halted = false) :
    stepSStmt (fuel + 12) state pending output eventLoop =
      .ok (state, pending, output, .suspended (.atEdge "trigger" .pos)
        [.forAfterBody trueCondition #[] eventBody]) := by
  rcases output with ⟨lines, current, strobes, halted, transfer, monitors⟩
  change halted = false at running
  subst halted
  change stepForLoop (fuel + 11) state pending
    { lines := lines, cur := current, pending := strobes, halted := false, transfer := transfer, monitors := monitors }
    trueCondition #[] eventBody = _
  rw [stepForLoop.eq_def]
  simp only [Bool.false_eq_true, if_false, evalForCondition, trueCondition,
    evalSExpr, evalExpr, Res.ok_bind, true_test, if_true]
  rfl

/-- A delayed body resumes at break, before the saved loop boundary. -/
theorem timer_retains (state : SvState) (pending : NbaQueue) (output : Out)
    (fuel : Nat) (running : output.halted = false) :
    stepSStmt (fuel + 12) state pending output timedLoop =
      .ok (state, pending, output, .suspended (.atTime 2)
        [.breakLoop, .forAfterBody trueCondition #[] breakBody]) := by
  rcases output with ⟨lines, current, strobes, halted, transfer, monitors⟩
  change halted = false at running
  subst halted
  change stepForLoop (fuel + 11) state pending
    { lines := lines, cur := current, pending := strobes, halted := false, transfer := transfer, monitors := monitors }
    trueCondition #[] breakBody = _
  rw [stepForLoop.eq_def]
  simp only [Bool.false_eq_true, if_false, evalForCondition, trueCondition,
    evalSExpr, evalExpr, Res.ok_bind, true_test, if_true]
  rfl

/-- Reaching break after the timer exits without entering another iteration. -/
theorem resumed_break_exits (state : SvState) (pending : NbaQueue) (output : Out)
    (fuel : Nat) (running : output.halted = false) :
    stepSStmts (fuel + 12) state pending output
        [.breakLoop, .forAfterBody trueCondition #[] breakBody] =
      .ok (state, pending, { output with transfer := .normal }, .done) := by
  rcases output with ⟨lines, current, strobes, halted, transfer, monitors⟩
  change halted = false at running
  subst halted
  rfl

/-- After an event body completes, the next iteration rearms its event wait. -/
theorem next_iteration_rearms (state : SvState) (pending : NbaQueue) (output : Out)
    (fuel : Nat) (running : output.halted = false)
    (normal : output.transfer = .normal) :
    stepSStmt (fuel + 12) state pending output
        (.forAfterBody trueCondition #[] eventBody) =
      .ok (state, pending, { output with transfer := .normal },
        .suspended (.atEdge "trigger" .pos)
          [.forAfterBody trueCondition #[] eventBody]) := by
  rcases output with ⟨lines, current, strobes, halted, transfer, monitors⟩
  change halted = false at running
  subst halted
  change transfer = .normal at normal
  subst transfer
  change stepForLoop (fuel + 11) state pending
    { lines := lines, cur := current, pending := strobes, halted := false, transfer := .normal, monitors := monitors }
    trueCondition #[] eventBody = _
  rw [stepForLoop.eq_def]
  simp only [Bool.false_eq_true, if_false, evalForCondition, trueCondition,
    evalSExpr, evalExpr, Res.ok_bind, true_test, if_true]
  rfl

#print axioms event_retains
#print axioms timer_retains
#print axioms resumed_break_exits
#print axioms next_iteration_rearms
#print axioms stepSStmt_done_agrees

partial def containsStatement (wanted : SStmt) (statement : SStmt) : Bool :=
  statement == wanted || match statement with
  | .block statements => statements.any (containsStatement wanted)
  | .ifStmt _ yes no => containsStatement wanted yes || no.any (containsStatement wanted)
  | .forLoop _ _ _ body | .repeatLoop _ _ body => containsStatement wanted body
  | _ => false

-- SYNTHETIC-ORACLE: tests=forever-fuel | origin=spec | authority=fueled-executor-contract | map=nonterminating-empty-loop:timeout
#guard execSStmt 64 [] [] {} (.forLoop #[] trueCondition #[] .skip) == .timeout

-- Complete independently observed source transcripts, 2026-10-20.
-- values.sv SHA-256: 9e407c392a7296abd122ff8b8289bb79356fc85a6b8143399ec4936ed8127679
-- timers.sv SHA-256: c019be4e1f9bcdfbdeaabaeaccdc2d6b37531e4d18e8b7721cb71dcdeb24970c
-- waits.sv SHA-256: 58c8ad59f3e4d124373293f5c871b410b2f4bf7dbfcfa8a7d7cba821a5c18a4d
def fixtureReceipt : IO Unit := do
  let .ok values := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/forever_loops/values.sv.json")
    | throw (IO.userError "forever values failed to load")
  unless runSelfCheck values 32768 == .ok
      ["transfers 5 12 2", "nested 3 3", "fresh 3 15", "halt 12"] do
    throw (IO.userError "forever values complete transcript differs")
  for (name, certificate, expected) in [
      ("timers", timedLoop, ["visit 1 1xz0", "visit 2 z01x", "visit 3 z01x",
        "visit 4 10xz", "done 4 10 4 10xz", "after_break 4"]),
      ("waits", eventLoop, ["blocked 0"])] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/forever_loops/{name}.sv.json")
      | throw (IO.userError s!"{name} failed to load")
    unless design.procs.any (fun process => match process with
        | .initial body => containsStatement certificate body
        | _ => false) do
      throw (IO.userError s!"{name} certificate differs from compiled source")
    for oracle in [ρ_src, ρ_rev] do
      let .ok world := elabTimedDesign 32768 design
        | throw (IO.userError s!"{name} timed design refused")
      let .ok (.ok _, world) := SvM.exec (slotStep oracle 32768) world
        | throw (IO.userError s!"{name} initial slot refused")
      let mut world := world
      for _ in List.range 20 do
        if world.out.halted then break
        let .ok (.ok _, next) := SvM.exec
            (do advanceTime 1; wakeTimers; slotStep oracle 32768) world
          | throw (IO.userError s!"{name} resumed slot refused")
        world := next
      unless world.out.halted && world.out.flush == expected do
        throw (IO.userError s!"{name} complete transcript differs: halted={world.out.halted} time={world.time} flush={repr world.out.flush}")

#eval fixtureReceipt

end Examples.systemVerilog.foreverLoops.proof
