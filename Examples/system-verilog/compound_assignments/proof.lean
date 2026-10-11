import LeanModels.Sv.SelfCheck
import LeanModels.Sv.Obs

namespace Examples.systemVerilog.compoundAssignments.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

def compoundBody : SStmt :=
  .block #[
    .m0 (.blockingAssign "value" (.lit (.ofNat 4 1))),
    .m0 (.blockingAssign "delta" (.lit (.ofNat 4 3))),
    .m0 (.blockingAssign "value" (.binary .add (.ident "value") (.ident "delta"))),
    .m0 (.blockingAssign "value" (.binary .sub (.ident "value") (.lit (.ofNat 4 1)))),
    .m0 (.blockingAssign "value" (.binary .and (.ident "value") (.lit (.ofNat 4 6)))),
    .m0 (.blockingAssign "value" (.binary .or (.ident "value") (.lit (.ofNat 4 8)))),
    .m0 (.blockingAssign "value" (.binary .xor (.ident "value") (.lit (.ofNat 4 3))))]

def runCompound : Res (SvState × NbaQueue × Out) :=
  execSStmt 64 [ ("value", .ofNat 4 0), ("delta", .ofNat 4 0) ] [] {}
    compoundBody

theorem compound_updates :
    runCompound = .ok
      ([ ("value", .ofNat 4 9), ("delta", .ofNat 4 3) ], [], {}) := by
  have add : (.ofNat 4 1 : LVec).add (.ofNat 4 3) = .ofNat 4 4 := by
    simp [LVec.add, LVec.toNat?_ofNat, LVec.arithWidth, LVec.width_ofNat]
  have sub : (.ofNat 4 4 : LVec).sub (.ofNat 4 1) = .ofNat 4 3 := by
    simp [LVec.sub, LVec.toNat?_ofNat, LVec.arithWidth, LVec.width_ofNat]
    rw [← LVec.ofNat_emod]
  have band : (.ofNat 4 3 : LVec).and (.ofNat 4 6) = .ofNat 4 2 := by
    simp [LVec.and, LVec.zipWith, LVec.ofNat, LVec.width]
    apply Array.ext'
    simp [List.ofFn_succ, List.zipWith, Logic.and]
    decide
  have bor : (.ofNat 4 2 : LVec).or (.ofNat 4 8) = .ofNat 4 10 := by
    simp [LVec.or, LVec.zipWith, LVec.ofNat, LVec.width]
    apply Array.ext'
    simp [List.ofFn_succ, List.zipWith, Logic.or]
    decide
  have bxor : (.ofNat 4 10 : LVec).xor (.ofNat 4 3) = .ofNat 4 9 := by
    simp [LVec.xor, LVec.zipWith, LVec.ofNat, LVec.width]
    apply Array.ext'
    simp [List.ofFn_succ, List.zipWith, Logic.xor]
    decide
  simp [runCompound, compoundBody, execSStmt, execSStmts, execStmt, evalExpr,
    readSignal, SvState.lookup, SvState.set, evalBinOp, add, sub, band, bor,
    bxor, Bind.bind, Pure.pure]

#print axioms compound_updates

#eval do
  let text ← IO.FS.readFile
    "Examples/system-verilog/compound_assignments/updates.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "real compound-assignment fixture failed to load")
  let some (SProc.initial body) := design.procs[0]?
    | throw (IO.userError "real compound-assignment process shape changed")
  let .block statements := body
    | throw (IO.userError "real compound-assignment body did not stay in the mixed self-check block")
  let .block expected := compoundBody
    | throw (IO.userError "compound-assignment certificate shape changed")
  for index in [0, 1, 2, 3, 4, 5, 6] do
    unless statements[index]? == expected[index]? do
      throw (IO.userError s!"compound-assignment statement {index} changed")
  unless runSelfCheck design 4096 == Res.ok ["PASS"] do
    throw (IO.userError "real compound-assignment fixture did not print PASS")

end Examples.systemVerilog.compoundAssignments.proof
