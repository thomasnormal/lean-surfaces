import LeanModels.Sv.Step

namespace Examples.systemVerilog.loops.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def orderLoop : SStmt :=
  .forLoop #[
    .m0 (.blockingAssign "index" (.lit (.ofNat 32 0))),
    .m0 (.blockingAssign "initializer"
      (.binary .add (.ident "initializer") (.lit (.ofNat 32 1)))),
    .m0 (.blockingAssign "mirror" (.ident "index"))]
    (.scmp .lt (.m0 (.ident "index")) (.m0 (.lit (.ofNat 32 4))))
    #[.m0 (.blockingAssign "index"
        (.binary .add (.ident "index") (.lit (.ofNat 32 1)))),
      .m0 (.blockingAssign "mirror" (.ident "index"))]
    (.m0 (.blockingAssign "total" (.binary .add (.ident "total") (.ident "mirror"))))

theorem ordered_header :
    execSStmt 128
      [("initializer", .ofNat 32 0), ("total", .ofNat 32 0)] [] {} orderLoop =
    .ok ([("initializer", .ofNat 32 1), ("total", .ofNat 32 6),
      ("index", .ofNat 32 4), ("mirror", .ofNat 32 4)], [], {}) := by
  have sign0 : msb (LVec.ofNat 32 0) = .l0 := by
    simp [msb, LVec.ofNat, Array.back?_eq_getElem?] <;> decide
  have sign1 : msb (LVec.ofNat 32 1) = .l0 := by
    simp [msb, LVec.ofNat, Array.back?_eq_getElem?] <;> decide
  have sign2 : msb (LVec.ofNat 32 2) = .l0 := by
    simp [msb, LVec.ofNat, Array.back?_eq_getElem?] <;> decide
  have sign3 : msb (LVec.ofNat 32 3) = .l0 := by
    simp [msb, LVec.ofNat, Array.back?_eq_getElem?] <;> decide
  have sign4 : msb (LVec.ofNat 32 4) = .l0 := by
    simp [msb, LVec.ofNat, Array.back?_eq_getElem?] <;> decide
  simp [orderLoop, execSStmt, execSStmts, execStmt, evalExpr,
    evalSExpr, evalForCondition, evalBinOp, evalScmp, scmpOp, toIntS?, sign0, sign1, sign2, sign3, sign4, readSignal,
    SvState.lookup, SvState.set, LVec.add, LVec.toNat?_ofNat,
    LVec.arithWidth, LVec.width_ofNat, LVec.condTrue, LVec.ofLogic,
    transferRest, SStmt.isLoopBoundary]
  repeat
    rw [execForLoop.eq_def]
    simp [execSStmt, execSStmts, execStmt, evalExpr, evalSExpr, evalBinOp,
      evalForCondition, evalScmp, scmpOp, toIntS?, sign0, sign1, sign2, sign3, sign4, readSignal,
      SvState.lookup, SvState.set, LVec.add, LVec.toNat?_ofNat,
      LVec.arithWidth, LVec.width_ofNat, LVec.condTrue, LVec.ofLogic,
      transferRest, SStmt.isLoopBoundary]

theorem for_wait_retains (state : SvState) (pending : NbaQueue) (output : Out)
    (running : output.halted = false) (steps : Array SStmt) (signal : String) (edge : Edge) :
    stepForLoop 8 state pending output (.m0 (.lit (.ofLogic .l1))) steps
      (.waitEvent signal edge) =
    .ok (state, pending, output, .suspended (.atEdge signal edge)
      [.forAfterBody (.m0 (.lit (.ofLogic .l1))) steps (.waitEvent signal edge)]) := by
  simp [stepForLoop, stepSStmt, evalSExpr, evalForCondition, evalExpr, running, LVec.ofLogic, LVec.condTrue]

theorem repeat_wait_retains (state : SvState) (pending : NbaQueue) (output : Out)
    (running : output.halted = false) (remaining amount : Nat) :
    stepRepeatLoop 8 state pending output (remaining + 1) (.delay amount) =
    .ok (state, pending, output, .suspended (.atTime amount)
      [.repeatAfterBody (remaining + 1) (.delay amount)]) := by
  simp [stepRepeatLoop, stepSStmt, running]

def waitingFor : SStmt :=
  .forLoop #[.m0 (.blockingAssign "index" (.lit (.ofNat 4 0)))]
    (.m0 (.binary .lt (.ident "index") (.lit (.ofNat 4 2))))
    #[.m0 (.blockingAssign "index" (.binary .add (.ident "index") (.lit (.ofNat 4 1))))]
    (.block #[.waitEvent "event" .pos, .continueLoop,
      .m0 (.blockingAssign "index" (.lit (.ofNat 4 9)))])

#guard match stepSStmt 128 [] [] {} waitingFor with
  | .ok (state, _, _, .suspended (.atEdge "event" .pos) residual) =>
      SvState.lookup state "index" == some (.ofNat 4 0) &&
      match stepSStmts 128 state [] {} residual with
      | .ok (next, _, _, .suspended (.atEdge "event" .pos) residual') =>
          SvState.lookup next "index" == some (.ofNat 4 1) &&
          match stepSStmts 128 next [] {} residual' with
          | .ok (final, _, output, .done) =>
              SvState.lookup final "index" == some (.ofNat 4 2) &&
              output.transfer == .normal
          | _ => false
      | _ => false
  | _ => false

def waitingRepeat : SStmt :=
  .repeatLoop (.m0 (.ident "count")) false
    (.block #[.delay 1, .m0 (.blockingAssign "count" (.lit (.ofNat 4 0))),
      .continueLoop, .finish])

#guard match stepSStmt 128 [("count", .ofNat 4 2)] [] {} waitingRepeat with
  | .ok (state, _, _, .suspended (.atTime 1) residual) =>
      match stepSStmts 128 state [] {} residual with
      | .ok (next, _, _, .suspended (.atTime 1) residual') =>
          SvState.lookup next "count" == some (.ofNat 4 0) &&
          match stepSStmts 128 next [] {} residual' with
          | .ok (_, _, output, .done) => !output.halted && output.transfer == .normal
          | _ => false
      | _ => false
  | _ => false

#guard repeatCount (.lit "x001") false == .ok 1
#guard repeatCount (.lit "xxxx") false == .ok 0
#guard repeatCount (.ofNat 64 4294967297) false == .ok 1
#guard repeatCount (.ofNat 64 4294967295) false == .ok 0
#guard repeatCount (.ofNat 4 15) true == .ok 0
#guard repeatCount (.ofNat 64 3) false == .ok 3
#guard sampleRepeatCount 8 [("count", .ofNat 64 3)]
    (.m0 (.ident "count")) false == .ok 3
#guard sampleRepeatCount 8 [("count", .ofNat 4 15)]
    (.m0 (.ident "count")) true == .ok 0
#guard evalForCondition 8 [("count", .ofNat 4 1)]
    (.m0 (.ident "count")) == .ok (.ofNat 4 1)

#eval do
  for fixture in ["order", "counts", "transfers"] do
    let text ← IO.FS.readFile s!"harness/sv/loops/{fixture}.sv.json"
    let .ok design := loadEnvelopeDesign text
      | throw (IO.userError s!"loop fixture {fixture} failed to load")
    unless runSelfCheck design 4096 == Res.ok ["PASS"] do
      throw (IO.userError s!"loop fixture {fixture} failed")
    if fixture == "order" then
      let some (SProc.initial (SStmt.block statements)) := design.procs[0]?
        | throw (IO.userError "ordered loop process changed")
      unless statements[2]? == some orderLoop do
        throw (IO.userError "ordered loop certificate differs from its source")

#print axioms ordered_header
#print axioms for_wait_retains
#print axioms repeat_wait_retains
#print axioms stepForLoop_done_agrees
#print axioms stepRepeatLoop_done_agrees

end Examples.systemVerilog.loops.proof
