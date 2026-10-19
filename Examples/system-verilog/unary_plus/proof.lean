import LeanModels.Sv.SelfCheck
import LeanModels.Sv.Param2
import LeanModels.Sv.Tests

namespace Examples.systemVerilog.unaryPlus.proof

open LeanModels.Sv

set_option autoImplicit false

/-- Certified below against the actual continuous assignment to `b`. -/
def sourceExpression : Expr := .unary .pos (.ident "a")

/-- The real assignment preserves every fully known input. -/
theorem known_input (value : LVec) (fuel : Nat) (h : value.allKnown = true) :
    evalExpr (fuel + 2) [("a", value)] sourceExpression = .ok value := by
  change Res.ok value.pos = _
  simp [LVec.pos, h]

/-- A single x/z bit poisons every output bit of the real assignment. -/
theorem unknown_input (value : LVec) (fuel : Nat) (h : value.allKnown = false) :
    evalExpr (fuel + 2) [("a", value)] sourceExpression = .ok (LVec.xVec value.width) := by
  change Res.ok value.pos = _
  simp [LVec.pos, h]

#print axioms known_input
#print axioms unknown_input

/-! These checks distinguish arithmetic collapse from operand erasure in
both symbolic compilers, including their nested arithmetic-operand paths.
The independent source fixture checks the same x/z rule.
REFERENCE: see arithmetic.sv, group unary-plus-arithmetic. -/

def nestedOperand : PExpr :=
  .binary (.m0 .div)
    (.binary (.m0 .and) (.unary .plus (.ident "a")) (.lit (.lit "1000")))
    (.lit (.lit "0001"))

#guard evalExpr 64 [("a", .lit "0x01")]
  (instExpr { widths := [("a", 4)] } (some 4) nestedOperand) == .ok (.lit "xxxx")
#guard evalExpr2 64 [("a", .lit "0x01")]
  (instExpr2 { widths := [("a", 4)] } [] (some 4) nestedOperand) == .ok (.lit "xxxx")

#eval show IO Unit from do
  let design ← EnvelopeIngest.loadFile "Examples/system-verilog/unary_plus/unary_plus.sv.json"
  unless design.processes[0]? == some (.assign "b" sourceExpression) && !design.hasUnsupported do
    throw (IO.userError "unary-plus source expression differs from its theorem")
  let text ← IO.FS.readFile "Examples/system-verilog/unary_plus/arithmetic.sv.json"
  let .ok fixture := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unary-plus arithmetic fixture failed to load")
  unless SelfCheck.runSelfCheck fixture 4096 == .ok ["PASS"] do
    throw (IO.userError "unary-plus arithmetic fixture disagrees")

end Examples.systemVerilog.unaryPlus.proof
