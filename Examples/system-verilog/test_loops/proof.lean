import LeanModels.Sv.Load

namespace Examples.systemVerilog.testLoops.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def falseCondition : SExpr := .m0 (.lit (.ofNat 32 0))
def writeValue : SStmt := .m0 (.blockingAssign "proof_value" (.lit (.ofNat 8 90)))
def pretest : SStmt := .forLoop #[] falseCondition #[] writeValue
def posttest : SStmt := .doWhileLoop falseCondition writeValue
def breaking : SStmt := .doWhileLoop (.m0 (.ident "guard")) .breakLoop
def waiting : SStmt := .doWhileLoop falseCondition (.waitEvent "trigger" .pos)

private theorem false_test : (LVec.ofNat 32 0).condTrue = false := by
  simp only [LVec.condTrue, LVec.ofNat, ← Array.any_toList]
  simp [Array.toList_ofFn, List.ofFn_succ,
    show (Logic.l0 == Logic.l1) = false from rfl]

/-- An initially false while leaves arbitrary state, pending work and output intact. -/
theorem pretest_preserves (state : SvState) (pending : NbaQueue) (output : Out)
    (fuel : Nat) :
    execSStmt (fuel + 8) state pending output pretest = .ok (state, pending, output) := by
  unfold pretest
  rw [execSStmt.eq_def]
  by_cases halted : output.halted = true
  · simp [halted]
  · simp only [halted]
    simp only [execSStmts, Res.ok_bind]
    rw [execForLoop.eq_def]
    simp [halted, evalForCondition, falseCondition, evalSExpr, evalExpr, false_test]

/-- A false post-test still permits exactly the first assignment. -/
theorem posttest_writes (state : SvState) (pending : NbaQueue) (output : Out)
    (fuel : Nat) (running : output.halted = false) :
    execSStmt (fuel + 8) state pending output posttest =
      .ok (SvState.set state "proof_value" (.ofNat 8 90), pending,
        { output with transfer := .normal }) := by
  simp [posttest, writeValue, falseCondition, execSStmt, execStmt, execForLoop,
    evalForCondition, evalSExpr, evalExpr, running, false_test]

/-- Break does not even read the post-test variable, which may be absent in this frame. -/
theorem break_skips_test (state : SvState) (pending : NbaQueue) (output : Out)
    (fuel : Nat) (running : output.halted = false) :
    execSStmt (fuel + 8) state pending output breaking =
      .ok (state, pending, { output with transfer := .normal }) := by
  simp [breaking, execSStmt, running]

/-- The first body wait retains its post-test boundary and all prior effects. -/
theorem first_wait_retains (state : SvState) (pending : NbaQueue) (output : Out)
    (fuel : Nat) (running : output.halted = false) :
    stepSStmt (fuel + 8) state pending output waiting =
      .ok (state, pending, output, .suspended (.atEdge "trigger" .pos)
        [.forAfterBody falseCondition #[] (.waitEvent "trigger" .pos)]) := by
  simp [waiting, stepSStmt, running]

#print axioms pretest_preserves
#print axioms posttest_writes
#print axioms break_skips_test
#print axioms first_wait_retains
#print axioms stepSStmt_done_agrees

-- SYNTHETIC-ORACLE: tests=internal-edge-admission | origin=spec | authority=timed-loader-contract | map=possible-procedural-write:requires-publication-rule
private def needsPublication (body : SStmt) : Bool :=
  requiresInternalEdges
    { name := "admission"
    , decls := #[]
    , procs := #[.initial (.waitEvent "watched" .any), .initial body] }

#guard needsPublication (.m0 (.nbaAssign "watched" (.lit (.ofNat 1 1))))
#guard needsPublication (.selectedAssign "watched" 1 true false false
  (.m0 (.lit (.ofNat 32 0))) (.m0 (.lit (.ofNat 1 1))))
#guard needsPublication (.packedAssign [.whole "watched" 1 false]
  (.m0 (.lit (.ofNat 1 1))))
#guard needsPublication (.scanf (.m0 (.lit (.ofNat 8 49))) [] []
  [.whole "watched" 1 false])
#guard !needsPublication (.m0 (.blockingAssign "other" (.lit (.ofNat 1 1))))

-- Complete independently observed source transcripts, 2026-10-20.
-- values.sv SHA-256: dbe625214394cb90bb5c8504e4cbd43bca9d1d2fd46604d406bc40d90860c385
-- waits.sv SHA-256: 49ab07391b22ce0f0afdf090aa344fb31b12a2e71f25c6d433fb180751f2aadb
-- timers.sv SHA-256: b902f8daa6b6f8451fd543e003387a77caf321bcb3e27f98ccc8026650f631b5
def fixtureReceipt : IO Unit := do
  let .ok values := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/test_loops/values.sv.json")
    | throw (IO.userError "test-loop values failed to load")
  let some (SProc.initial (.block statements)) := values.procs[0]?
    | throw (IO.userError "test-loop values process shape changed")
  unless [pretest, posttest, breaking].all statements.contains do
    throw (IO.userError "test-loop certificates differ from extracted source")
  unless runSelfCheck values 4096 == Res.ok [
      "while_false 0", "do_false 1", "while_unknown 0", "do_unknown 1",
      "while_known_one 1", "do_continue 5 12", "while_continue 5 12",
      "do_break 1", "while_break 1", "nested 2 2", "pretest a5", "posttest 5a"] do
    throw (IO.userError "test-loop values disagree")
  let .ok internalEdges := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/test_loops/waits.sv.json")
    | throw (IO.userError "test-loop waits failed to load")
  let some (SProc.initial (.block waitStatements)) := internalEdges.procs[0]?
    | throw (IO.userError "test-loop waits process shape changed")
  unless waitStatements.contains waiting do
    throw (IO.userError "first-wait certificate differs from extracted source")
  unless requiresInternalEdges internalEdges do
    throw (IO.userError "internal edge census was lost")
  for oracle in [ρ_src, ρ_rev] do
    let .ok world := elabTimedDesign 4096 internalEdges
      | throw (IO.userError "test-loop edge fixture failed to elaborate")
    let .ok (.ok _, world) := SvM.exec (slotStep oracle 4096) world
      | throw (IO.userError "test-loop edge initial slot refused")
    let mut world := world
    for _ in List.range 5 do
      if world.out.halted then break
      let .ok (.ok _, next) := SvM.exec
          (do advanceTime 1; wakeTimers; slotStep oracle 4096) world
        | throw (IO.userError "test-loop edge resumed slot refused")
      world := next
    unless world.out.halted && world.out.flush ==
        ["while_wait 1", "do_wait 1", "event 1 1"] do
      throw (IO.userError s!"test-loop edge transcript differs: {repr world.out.flush}")
  let .ok waits := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/test_loops/timers.sv.json")
    | throw (IO.userError "test-loop timers failed to load")
  for oracle in [ρ_src, ρ_rev] do
    let .ok world := elabTimedDesign 4096 waits
      | throw (IO.userError "test-loop timed loading refused")
    let .ok (.ok _, world) := SvM.exec (slotStep oracle 4096) world
      | throw (IO.userError "test-loop initial slot refused")
    let mut world := world
    for _ in List.range 8 do
      if world.out.halted then break
      let .ok (.ok _, next) := SvM.exec
          (do advanceTime 1; wakeTimers; slotStep oracle 4096) world
        | throw (IO.userError "test-loop resumed slot refused")
      world := next
    unless world.out.flush == ["while_wait 1", "do_wait 1"] do
      throw (IO.userError s!"test-loop resumed transcript disagrees: {repr world.out.flush}")

#eval fixtureReceipt

end Examples.systemVerilog.testLoops.proof
