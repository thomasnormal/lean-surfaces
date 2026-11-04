import LeanModels.Sv.Ingest2
import LeanModels.Sv.Param2
import LeanModels.Sv.SelfCheck
import LeanModels.Sv.Obs

namespace Examples.systemVerilog.remainder.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

load_design_sv2 remainder from "Examples/system-verilog/remainder/remainder_sv2.json"
load_design_sv2 signedRemainder from "Examples/system-verilog/remainder/signed_remainder.sv.json"

def remainderSource (design : PDesign) : PExpr :=
  match design.processes with
  | [.assign "result" value] => value
  | _ => .unsupported "Remainder:shape" "continuous assignment changed"

theorem unsigned_source :
    remainderSource remainder.pdesign =
      .binary (.m0 .rem) (.ident "left") (.ident "right") := rfl

theorem signed_source :
    remainderSource signedRemainder.pdesign =
      .binary (.m0 .srem) (.ident "left") (.ident "right") := rfl

def remainderExpr (signed : Bool) (width : Nat) : Expr :=
  instExpr { widths := [("left", width), ("right", width)] }
    (some width)
    (remainderSource (if signed then signedRemainder.pdesign else remainder.pdesign))

theorem unsigned_instantiation (width : Nat) :
    remainderExpr false width = .binary .rem (.ident "left") (.ident "right") := by
  change instExpr { widths := [("left", width), ("right", width)] }
    (some width) (remainderSource remainder.pdesign) = _
  rw [unsigned_source]
  simp [instExpr, instDivOperand, divOperandWidth, fitDivOperand, List.lookup]

theorem signed_instantiation (width : Nat) :
    remainderExpr true width = .binary .srem (.ident "left") (.ident "right") := by
  change instExpr { widths := [("left", width), ("right", width)] }
    (some width) (remainderSource signedRemainder.pdesign) = _
  rw [signed_source]
  simp [instExpr, instDivOperand, divOperandWidth, fitDivOperand, List.lookup]

def runRemainder {width : Nat} (signed : Bool) (left right : BitVec width) : Res LVec :=
  evalExpr 8 [("left", .ofBitVec left), ("right", .ofBitVec right)]
    (remainderExpr signed width)

theorem unsigned_remainder {width : Nat} (left right : BitVec width)
    (nonzero : right.toNat ≠ 0) :
    runRemainder false left right = .ok (.ofBitVec (left % right)) := by
  simp [runRemainder, unsigned_instantiation, evalExpr, evalBinOp,
    readSignal, SvState.lookup, LVec.rem_ofBitVec, nonzero]

theorem signed_remainder {width : Nat} (left right : BitVec width)
    (nonzero : right.toNat ≠ 0) :
    runRemainder true left right = .ok (.ofBitVec (left.srem right)) := by
  simp [runRemainder, signed_instantiation, evalExpr, evalBinOp,
    readSignal, SvState.lookup, LVec.srem_ofBitVec, nonzero]

#print axioms unsigned_remainder
#print axioms signed_remainder

#guard runRemainder false (13 : BitVec 8) (5 : BitVec 8) == .ok (.ofNat 8 3)
#guard runRemainder true (-13 : BitVec 8) (5 : BitVec 8) == .ok (.ofInt 8 (-3))
#guard runRemainder true (-13 : BitVec 8) (-5 : BitVec 8) == .ok (.ofInt 8 (-3))
#guard runRemainder false (13 : BitVec 8) (0 : BitVec 8) == .ok (.xVec 8)
#guard runRemainder true (0 : BitVec 8) (0 : BitVec 8) == .ok (.xVec 8)
#guard instExpr {} (some 16) (.binary .mod (.int 13) (.int 5)) == .lit (.ofInt 16 3)
#guard (match instExpr { widths := [("left", 8), ("right", 8)] }
    (some 8) (.binary .mod (.ident "left") (.ident "right")) with
  | .unsupported .. => true
  | _ => false)
#guard (match instExpr2 { widths := [("left", 8), ("right", 8)] } []
    (some 8) (.binary .mod (.ident "left") (.ident "right")) with
  | .unsupported .. => true
  | _ => false)

end Examples.systemVerilog.remainder.proof
