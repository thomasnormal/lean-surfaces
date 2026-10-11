import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.packedAssignmentTargets.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

def unknownStatement : SStmt :=
  .selectedAssign "value" 1 false false false
    (.m0 (.ident "index")) (.m0 (.lit (.lit "0")))

def unknownFrame (value : LVec) : SvState :=
  [("value", value), ("index", .lit "xxxx")]

def writeUnknown (value : LVec) : Res (SvState × NbaQueue × Out) :=
  execSStmt 16 (unknownFrame value) [] {} unknownStatement

#eval do
  let text ← IO.FS.readFile
    "Examples/system-verilog/packed_assignment_targets/runtime_updates.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "real packed-write fixture failed to load")
  let some (SProc.initial (SStmt.block statements)) := design.procs[0]?
    | throw (IO.userError "real packed-write process shape changed")
  let some statement := statements[8]?
    | throw (IO.userError "real packed-write assignment disappeared")
  unless statement == unknownStatement do
    throw (IO.userError "proved selected assignment differs from the real fixture")
  unless runSelfCheck design 4096 == Res.ok ["PASS"] do
    throw (IO.userError "real packed-write fixture did not print PASS")

theorem unknown_index_preserves_state (value : LVec) :
    writeUnknown value = .ok (unknownFrame value, [], {}) := by
  have index_unknown : selectedIndex false (.lit "xxxx") = none := by
    change selectedIndex false ⟨#[.lx, .lx, .lx, .lx]⟩ = none
    simp [selectedIndex, LVec.toNat?, LVec.allKnown, Logic.isKnown]
  simp [writeUnknown, unknownStatement, unknownFrame, execSStmt, evalSExpr,
    evalExpr, readSignal, SvState.lookup, selectedWrite, index_unknown, SvState.set,
    Bind.bind, Pure.pure]

#print axioms unknown_index_preserves_state

def aliasStatement : SStmt :=
  .packedAssign [.whole "first" 4 false, .whole "first" 4 false]
    (.m0 (.lit (.lit "10100101")))

def writeAlias (value : LVec) (order : AssignmentOrder := rightToLeftAssignmentOrder) :
    Res (SvState × NbaQueue × Out) :=
  execSStmt 16 [("first", value)] [] {} aliasStatement order

#eval do
  let text ← IO.FS.readFile
    "Examples/system-verilog/packed_assignment_targets/concat_updates.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "real concatenated-write fixture failed to load")
  let some (SProc.initial (SStmt.block statements)) := design.procs[0]?
    | throw (IO.userError "real concatenated-write process shape changed")
  let some statement := statements[10]?
    | throw (IO.userError "real aliased concatenated assignment disappeared")
  unless statement == aliasStatement do
    throw (IO.userError "proved aliased assignment differs from the real fixture")
  unless runSelfCheck design 4096 == Res.ok ["PASS"] do
    throw (IO.userError "real concatenated-write fixture did not print PASS")

theorem alias_right_to_left (value : LVec) (width : value.width = 4) :
    writeAlias value = .ok ([("first", .lit "1010")], [], {}) := by
  have order : rightToLeftAssignmentOrder 2 = [1, 0] := rfl
  have valid : validAssignmentOrder 2 [1, 0] = true := rfl
  have resized : (.lit "10100101" : LVec).resizeU 8 = .lit "10100101" := rfl
  have low : (.lit "10100101" : LVec).extract 0 4 = .lit "0101" := rfl
  have high : (.lit "10100101" : LVec).extract 4 4 = .lit "1010" := rfl
  have low_width : (.lit "0101" : LVec).width = 4 := rfl
  simp [writeAlias, aliasStatement, execSStmt, evalSExpr, evalExpr,
    order, valid, packedTargetSlices,
    PackedTarget.width, execPackedTargets, SvState.lookup, SvState.set, width,
    resized, low, high, low_width, Bind.bind, Pure.pure]

theorem alias_invalid_order_refused (value : LVec) :
    writeAlias value (fun _ => [0, 0]) =
      .unsupported "concatenated assignment order must be a permutation of destinations" := by
  have invalid : validAssignmentOrder 2 [0, 0] = false := rfl
  simp [writeAlias, aliasStatement, execSStmt, evalSExpr, evalExpr,
    invalid, Bind.bind, Pure.pure]

#print axioms alias_right_to_left
#print axioms alias_invalid_order_refused

end Examples.systemVerilog.packedAssignmentTargets.proof
