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

def nbaStatement : SStmt :=
  .selectedNbaAssign "value" 1 false false false
    (.m0 (.ident "index")) (.m0 (.lit (.lit "1")))

def nbaBody : SStmt :=
  .block #[
    .m0 (.blockingAssign "value" (.lit (.lit "0000"))),
    .m0 (.blockingAssign "index" (.lit (.lit "01"))),
    nbaStatement,
    .m0 (.blockingAssign "index" (.lit (.lit "11"))),
    nbaStatement]

def writeNba : Res (SvState × NbaQueue × Out) :=
  execSStmt 64 [("value", .lit "xxxx"), ("index", .lit "00")] [] {} nbaBody

theorem selected_nba_snapshots :
    writeNba = .ok
      ([ ("value", .lit "0000"), ("index", .lit "11") ],
       [("value", .lit "0010"), ("value", .lit "1010")], {}) := by
  have z1 : (Logic.l0 == Logic.l1) = false := by rfl
  have o1 : (Logic.l1 == Logic.l1) = true := by rfl
  have n01 : (⟨#[.l1, .l0]⟩ : LVec).toNat? = some 1 := by
    simp [LVec.toNat?, LVec.allKnown, Logic.isKnown, LVec.toNat, z1, o1]
  have n11 : (⟨#[.l1, .l1]⟩ : LVec).toNat? = some 3 := by
    simp [LVec.toNat?, LVec.allKnown, Logic.isKnown, LVec.toNat, o1]
  have i1 : selectedIndex false (.lit "01") = some 1 := by
    change selectedIndex false ⟨#[.l1, .l0]⟩ = some 1
    simp [selectedIndex, n01]
  have i3 : selectedIndex false (.lit "11") = some 3 := by
    change selectedIndex false ⟨#[.l1, .l1]⟩ = some 3
    simp [selectedIndex, n11]
  have r1 : (.lit "1" : LVec).resizeU 1 = .lit "1" := by rfl
  have r1bits : (⟨#[.l1]⟩ : LVec).resizeU 1 = ⟨#[.l1]⟩ := by rfl
  have first : (.lit "0000" : LVec).insertAt 1 (.lit "1") = .lit "0010" := by rfl
  have second : (.lit "0010" : LVec).insertAt 3 (.lit "1") = .lit "1010" := by rfl
  have firstBits :
      (⟨#[.l0, .l0, .l0, .l0]⟩ : LVec).insertAt 1 ⟨#[.l1]⟩ =
        ⟨#[.l0, .l1, .l0, .l0]⟩ := by rfl
  have secondBits :
      (⟨#[.l0, .l1, .l0, .l0]⟩ : LVec).insertAt 3 ⟨#[.l1]⟩ =
        ⟨#[.l0, .l1, .l0, .l1]⟩ := by rfl
  simp [writeNba, nbaBody, nbaStatement, execSStmt, execSStmts,
    execStmt, evalSExpr, evalExpr, readSignal, enqueueSelectedNba,
    queuedValue, selectedWrite, selectedIndex, SvState.lookup, SvState.set,
    LVec.lit, LVec.ofString?, Logic.ofChar?, instBEqLogic, z1, o1, n01, n11,
    i1, i3, r1, r1bits, first, second, firstBits, secondBits,
    Bind.bind, Pure.pure]

#print axioms selected_nba_snapshots

#eval do
  let text ← IO.FS.readFile
    "Examples/system-verilog/packed_assignment_targets/nba_updates.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "real selected-NBA fixture failed to load")
  let some (SProc.initial (SStmt.block statements)) := design.procs[0]?
    | throw (IO.userError "real selected-NBA process shape changed")
  let some first := statements[2]?
    | throw (IO.userError "first selected-NBA statement disappeared")
  let some second := statements[4]?
    | throw (IO.userError "second selected-NBA statement disappeared")
  unless first == nbaStatement && second == nbaStatement do
    throw (IO.userError "proved selected-NBA statements differ from the real fixture")
  unless runSelfCheck design 4096 == Res.ok ["PASS"] do
    throw (IO.userError "real selected-NBA fixture did not print PASS")

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
