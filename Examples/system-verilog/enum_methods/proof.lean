import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.enumMethods.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The extracted `proof_result = proof_value.next()` assignment. -/
def nextExpression : SExpr :=
  .ternary (.caseEq (.m0 (.ident "proof_value")) (.m0 (.lit (.lit "0011"))))
    (.m0 (.lit (.lit "0111")))
    (.ternary (.caseEq (.m0 (.ident "proof_value")) (.m0 (.lit (.lit "0111"))))
      (.m0 (.lit (.lit "0001")))
      (.ternary (.caseEq (.m0 (.ident "proof_value")) (.m0 (.lit (.lit "0001"))))
        (.m0 (.lit (.lit "0011"))) (.m0 (.lit (.lit "xxxx")))))

private theorem ternary_case (condition : Logic) (yes no : LVec) :
    LVec.ternary (.ofLogic condition) yes no =
      match condition with
      | .l1 => yes
      | .l0 => no
      | _ => LVec.merge yes no := by
  cases condition <;>
    simp [LVec.ternary, LVec.ofLogic, LVec.condTrue, LVec.isKnownZero,
      show (Logic.l0 == Logic.l1) = false from rfl,
      show (Logic.l1 == Logic.l1) = true from rfl,
      show (Logic.lx == Logic.l1) = false from rfl,
      show (Logic.lz == Logic.l1) = false from rfl,
      show (Logic.l0 == Logic.l0) = true from rfl,
      show (Logic.lx == Logic.l0) = false from rfl,
      show (Logic.lz == Logic.l0) = false from rfl]

/-- Every value outside the declared member set produces the base default. -/
theorem nonmember_default (value : LVec) (fuel : Nat)
    (notA : value.eqCase (.lit "0011") = .l0)
    (notB : value.eqCase (.lit "0111") = .l0)
    (notC : value.eqCase (.lit "0001") = .l0) :
    evalSExpr (fuel + 6) [("proof_value", value)] nextExpression =
      .ok (.lit "xxxx") := by
  simp [nextExpression, evalSExpr, evalExpr, readSignal, SvState.lookup,
    Bind.bind, Pure.pure, notA, notB, notC, ternary_case]

/-- The successor is the next declaration, even though the numeric order differs. -/
theorem first_successor (value : LVec) (fuel : Nat)
    (isA : value.eqCase (.lit "0011") = .l1) :
    evalSExpr (fuel + 6) [("proof_value", value)] nextExpression =
      .ok (.lit "0111") := by
  simp [nextExpression, evalSExpr, evalExpr, readSignal, SvState.lookup,
    Bind.bind, Pure.pure, isA, ternary_case]

#print axioms nonmember_default
#print axioms first_successor

-- Complete independently observed transcript, 2026-10-20. The source binding
-- and the extracted assignment are checked together below.
-- enum_methods.sv SHA-256:
-- 2b4c0cde79bb4546872463c33ea343b533eb5476fea7c9335ff61ca876096161
def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/enum_methods/enum_methods.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "enum-method fixture failed to load")
  let some (SProc.initial (.block statements)) := design.procs[0]?
    | throw (IO.userError "enum-method process shape changed")
  unless statements.contains (.assign false "proof_result" nextExpression) do
    throw (IO.userError "enum-method certificate differs from extracted source")
  unless runSelfCheck design 4096 == Res.ok [
      "ends 3 1 3", "wrap 7 1 1 7", "invalid4 x x x x", "invalid2 0 0 0 0",
      "unknown4 x x x x", "negative 3 3", "unknown_count 3 3",
      "named_x x10 z01 010 x10", "named_z z01 010 x10 z01",
      "wide_negative 3 3", "wide_truncate 7 1", "nested 3", "field 1 3 3 1",
      "cells 1 3", "generated 0 8 4 2", "signed -3 d", "proof_default x"] do
    throw (IO.userError "enum-method fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.enumMethods.proof
