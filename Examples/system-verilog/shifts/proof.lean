import LeanModels.Sv.Ingest2
import LeanModels.Sv.Param2
import LeanModels.Sv.SelfCheck
import LeanModels.Sv.Obs

namespace Examples.systemVerilog.shifts.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

load_design_sv2 shifts from "Examples/system-verilog/shifts/shifts.sv.json"

def shiftSource (name : String) : PExpr :=
  match shifts.pdesign.processes.find? (fun process =>
    match process with | .assign target _ => target == name | _ => false) with
  | some (.assign _ expression) => expression
  | _ => .unsupported "Shift:shape" "continuous assignment changed"

theorem logical_left_source :
    shiftSource "logical_left" =
      .binary (.m0 (.shl false)) (.ident "value") (.ident "amount") := rfl

theorem logical_right_source :
    shiftSource "logical_right" =
      .binary (.m0 (.shr false)) (.ident "value") (.ident "amount") := rfl

theorem arithmetic_left_source :
    shiftSource "arithmetic_left" =
      .binary (.m0 (.ashl false)) (.ident "value") (.ident "amount") := rfl

theorem arithmetic_right_source :
    shiftSource "arithmetic_right" =
      .binary (.m0 (.ashr true)) (.cast true (.resize 8 (.ident "value")))
        (.ident "amount") := rfl

def shiftExpr (name : String) (width amountWidth : Nat) : Expr2 :=
  instExpr2 { widths := [("value", width), ("amount", amountWidth)] } []
    (some width) (shiftSource name)

def runShift (name : String) (value amount : LVec) : Res LVec :=
  evalExpr2 16 [("value", value), ("amount", amount)]
    (shiftExpr name value.width amount.width)

theorem logical_left_instantiation (width amountWidth : Nat) :
    shiftExpr "logical_left" width amountWidth =
      .binary (.shl false) (.ident "value") (.ident "amount") := by
  unfold shiftExpr
  rw [logical_left_source]
  simp [instExpr2, instDivOperand2, divOperandWidth2, fitDivOperand2, List.lookup]

theorem logical_right_instantiation (width amountWidth : Nat) :
    shiftExpr "logical_right" width amountWidth =
      .binary (.shr false) (.ident "value") (.ident "amount") := by
  unfold shiftExpr
  rw [logical_right_source]
  simp [instExpr2, instDivOperand2, divOperandWidth2, fitDivOperand2, List.lookup]

theorem arithmetic_left_instantiation (width amountWidth : Nat) :
    shiftExpr "arithmetic_left" width amountWidth =
      .binary (.ashl false) (.ident "value") (.ident "amount") := by
  unfold shiftExpr
  rw [arithmetic_left_source]
  simp [instExpr2, instDivOperand2, divOperandWidth2, fitDivOperand2, List.lookup]

theorem arithmetic_right_instantiation (width amountWidth : Nat) :
    shiftExpr "arithmetic_right" width amountWidth =
      .binary (.ashr true) (.ident "value") (.ident "amount") := by
  unfold shiftExpr
  rw [arithmetic_right_source]
  simp [instExpr2, instDivOperand2, divOperandWidth2, fitDivOperand2, List.lookup]

theorem logical_left (value amount : LVec) :
    runShift "logical_left" value amount = .ok (value.shl amount) := by
  simp [runShift, logical_left_instantiation, evalExpr2, evalBinOp,
    readSignal, SvState.lookup]

theorem logical_right (value amount : LVec) :
    runShift "logical_right" value amount = .ok (value.shr amount) := by
  simp [runShift, logical_right_instantiation, evalExpr2, evalBinOp,
    readSignal, SvState.lookup]

theorem arithmetic_left (value amount : LVec) :
    runShift "arithmetic_left" value amount = .ok (value.shl amount) := by
  simp [runShift, arithmetic_left_instantiation, evalExpr2, evalBinOp,
    readSignal, SvState.lookup, LVec.ashl]

theorem arithmetic_right (value amount : LVec) :
    runShift "arithmetic_right" value amount = .ok (value.ashr true amount) := by
  simp [runShift, arithmetic_right_instantiation, evalExpr2, evalBinOp,
    readSignal, SvState.lookup]

theorem logical_left_bits (value amount : LVec) (count : Nat)
    (known : amount.toNat? = some count) :
    runShift "logical_left" value amount = .ok
      ⟨Array.ofFn (n := value.width) fun index =>
        if index.val < count then .l0 else value.bits[index.val - count]?.getD .l0⟩ := by
  rw [logical_left]
  simp [LVec.shl, LVec.shiftAmount?, known]

theorem logical_right_bits (value amount : LVec) (count : Nat)
    (known : amount.toNat? = some count) :
    runShift "logical_right" value amount = .ok
      ⟨Array.ofFn (n := value.width) fun index => value.bits[index.val + count]?.getD .l0⟩ := by
  rw [logical_right]
  simp [LVec.shr, LVec.shiftAmount?, known]

theorem arithmetic_right_bits (value amount : LVec) (count : Nat)
    (known : amount.toNat? = some count) :
    runShift "arithmetic_right" value amount = .ok
      ⟨Array.ofFn (n := value.width) fun index =>
        value.bits[index.val + count]?.getD (value.bits.back?.getD .l0)⟩ := by
  rw [arithmetic_right]
  simp [LVec.ashr, LVec.shiftAmount?, known]

theorem unknown_amount (value amount : LVec) (unknown : amount.toNat? = none) :
    runShift "logical_left" value amount = .ok (.xVec value.width) ∧
    runShift "logical_right" value amount = .ok (.xVec value.width) ∧
    runShift "arithmetic_left" value amount = .ok (.xVec value.width) ∧
    runShift "arithmetic_right" value amount = .ok (.xVec value.width) := by
  simp [logical_left, logical_right, arithmetic_left, arithmetic_right,
    LVec.shl, LVec.shr, LVec.ashr, LVec.shiftAmount?, unknown]

#print axioms logical_left_bits
#print axioms logical_right_bits
#print axioms arithmetic_right_bits
#print axioms unknown_amount

#guard runShift "logical_left" (.lit "1xz00101") (.ofNat 4 1) == .ok (.lit "xz001010")
#guard runShift "logical_right" (.lit "1xz00101") (.ofNat 4 1) == .ok (.lit "01xz0010")
#guard runShift "arithmetic_right" (.lit "z1000001") (.ofNat 4 1) == .ok (.lit "zz100000")
#guard runShift "arithmetic_right" (.lit "10000001") (.ofNat 4 8) == .ok (.lit "11111111")
#guard runShift "logical_left" (.lit "10000001") (.ofNat 32 0xffffffff) == .ok (.ofNat 8 0)
#guard runShift "logical_left" (.lit "10000001") (.lit "x001") == .ok (.xVec 8)
#guard runShift "logical_right" (.lit "10000001") (.lit "z001") == .ok (.xVec 8)
#guard instExpr {} (some 8) (.binary .shl (.int 3) (.int 2)) == .lit (.ofInt 8 12)
#guard instExpr2 {} [] (some 8) (.binary .ashr (.int (-8)) (.int 2)) == .lit (.ofInt 8 (-2))
#guard instExpr { widths := [("value", 8), ("amount", 4)] } (some 16)
    (shiftSource "logical_left") ==
  .binary (.shl false) (.concat #[.lit (.replicate 8 .l0), .ident "value"]) (.ident "amount")
#guard evalExpr2 32 [("value", .ofNat 8 129), ("amount", .ofNat 4 1)]
    (instExpr2 { widths := [("value", 8), ("amount", 4)] } [] (some 16)
      (shiftSource "arithmetic_right")) == .ok (.ofNat 16 65472)

end Examples.systemVerilog.shifts.proof
