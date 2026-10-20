import LeanModels.Sv.Ingest2
import LeanModels.Sv.Param2
import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.implication.proof

open LeanModels.Sv

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

load_design_sv2 implication from "Examples/system-verilog/implication/implication.sv.json"

def source : PExpr :=
  match implication.pdesign.processes with
  | [.assign "implied" value] => value
  | _ => .unsupported "Implication:source" "assignment changed"

theorem source_lowering :
    source = .binary .lor (.unary (.m0 .lnot) (.ident "left")) (.ident "right") := rfl

def sourceExpr (width : Nat) : Expr :=
  instExpr { widths := [("left", width), ("right", width)] } (some 65) source

def sourceExpr2 (width : Nat) : Expr2 :=
  instExpr2 { widths := [("left", width), ("right", width)] } [] (some 65) source

theorem source_instantiation (width : Nat) :
    sourceExpr width = .binary .lor (.unary .lnot (.ident "left")) (.ident "right") := by
  simp [sourceExpr, source_lowering, instExpr, selfWidth, List.lookup,
    show (SymBinOp.lor == SymBinOp.land) = false from rfl]

theorem source_instantiation2 (width : Nat) :
    sourceExpr2 width = .logical false (.unary .lnot (.ident "left")) (.ident "right") := by
  simp [sourceExpr2, source_lowering, instExpr2, selfWidth2, List.lookup,
    show (SymBinOp.lor == SymBinOp.land) = false from rfl]

private theorem truthy_one : LVec.truthy (.ofLogic .l1) = .l1 := by
  simp [LVec.truthy, LVec.hasKnownOne, LVec.ofLogic]

private theorem one_or (value : Logic) : Logic.or .l1 value = .l1 := by
  cases value <;> rfl

private theorem or_one (value : Logic) : Logic.or value .l1 = .l1 := by
  cases value <;> rfl

/-- A false antecedent makes the real assignment true at every source width. -/
theorem false_antecedent (left right : LVec) (width fuel : Nat)
    (falseLeft : left.lnot = .l1) :
    evalExpr (fuel + 3) [("left", left), ("right", right)] (sourceExpr width) =
      .ok (.ofLogic .l1) := by
  rw [source_instantiation]
  simp [evalExpr, evalUnaryOp, evalBinOp, readSignal, SvState.lookup,
    Bind.bind, Pure.pure, falseLeft, LVec.lor, truthy_one, one_or]

/-- A true consequent dominates even an unknown antecedent. -/
theorem true_consequent (left right : LVec) (width fuel : Nat)
    (trueRight : right.truthy = .l1) :
    evalExpr (fuel + 3) [("left", left), ("right", right)] (sourceExpr width) =
      .ok (.ofLogic .l1) := by
  rw [source_instantiation]
  simp [evalExpr, evalUnaryOp, evalBinOp, readSignal, SvState.lookup,
    Bind.bind, Pure.pure, LVec.lor, trueRight, or_one]

#print axioms false_antecedent
#print axioms true_consequent
#print axioms source_instantiation2

def scalarRows : List (Logic × Logic × Logic) := [
  (.l0, .l0, .l1), (.l0, .l1, .l1), (.l0, .lx, .l1), (.l0, .lz, .l1),
  (.l1, .l0, .l0), (.l1, .l1, .l1), (.l1, .lx, .lx), (.l1, .lz, .lx),
  (.lx, .l0, .lx), (.lx, .l1, .l1), (.lx, .lx, .lx), (.lx, .lz, .lx),
  (.lz, .l0, .lx), (.lz, .l1, .l1), (.lz, .lx, .lx), (.lz, .lz, .lx)]

def fixtureReceipt : IO Unit := do
  -- Independently observed scalar truth table, repeated at three source widths.
  for width in [1, 4, 65] do
    for (left, right, expected) in scalarRows do
      let state := [("left", LVec.replicate width left), ("right", LVec.replicate width right)]
      unless evalExpr 64 state (sourceExpr width) == .ok (.ofLogic expected) &&
          evalExpr2 64 state (sourceExpr2 width) == .ok (.ofLogic expected) do
        throw (IO.userError "compiled implication disagrees")
  let text ← IO.FS.readFile "Examples/system-verilog/implication/values.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "implication values fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == Res.ok [
      "00 1", "01 1", "0x 1", "0z 1", "10 0", "11 1", "1x x", "1z x",
      "x0 x", "x1 1", "xx x", "xz x", "z0 x", "z1 1", "zx x", "zz x",
      "vectors x", "zero 1", "wide 00000000000000001",
      "context 00000001 xxxxxxxx", "nested 1 0"] do
    throw (IO.userError "implication values fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.implication.proof
