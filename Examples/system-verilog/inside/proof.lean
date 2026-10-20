import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.inside.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The actual `proof_result` assignment's membership expression. -/
def membership : SExpr :=
  .logOr
    (.m0 (.binary .wildEq (.ident "proof_left") (.ident "proof_candidate")))
    (.m0 (.binary .wildEq (.ident "proof_left") (.ident "proof_mask")))

private theorem truthy_one : truthy (.ofLogic .l1) = .l1 := by
  simp [truthy, LVec.ofLogic, LVec.condTrue,
    show (Logic.l1 == Logic.l1) = true from rfl]

private theorem or_one (value : Logic) : Logic.or value .l1 = .l1 := by
  cases value <;> rfl

/-- A definite member dominates any ambiguous comparison with another item. -/
theorem definite_member (left candidate mask : LVec) (fuel : Nat)
    (matched : left.eqWildcard mask = .l1) :
    evalSExpr (fuel + 4)
      [("proof_left", left), ("proof_candidate", candidate), ("proof_mask", mask)]
      membership = .ok (.ofLogic .l1) := by
  simp [membership, evalSExpr, evalExpr, evalBinOp, readSignal,
    SvState.lookup, Bind.bind, Pure.pure, matched, truthy_one, or_one]

/-- An entirely wildcard item matches every same-width subject. -/
theorem all_wildcards (left candidate mask : LVec) (fuel : Nat)
    (sameWidth : left.width = mask.width)
    (wild : ∀ bit ∈ mask.bits, bit.isKnown = false) :
    evalSExpr (fuel + 4)
      [("proof_left", left), ("proof_candidate", candidate), ("proof_mask", mask)]
      membership = .ok (.ofLogic .l1) := by
  apply definite_member
  have mismatch : (Array.zip left.bits mask.bits).any
      (fun (x, y) => y.isKnown && x.isKnown && x != y) = false := by
    apply Array.any_eq_false'.mpr
    rintro ⟨x, y⟩ h
    simp [wild y (Array.of_mem_zip h).2]
  have unknown : (Array.zip left.bits mask.bits).any
      (fun (x, y) => y.isKnown && !x.isKnown) = false := by
    apply Array.any_eq_false'.mpr
    rintro ⟨x, y⟩ h
    simp [wild y (Array.of_mem_zip h).2]
  unfold LVec.eqWildcard
  rw [if_neg (fun h => h sameWidth)]
  dsimp only
  rw [mismatch, unknown]
  rfl

#print axioms definite_member
#print axioms all_wildcards

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/inside/inside.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "integral membership fixture failed to load")
  let some (SProc.initial (.block statements)) := design.procs[0]?
    | throw (IO.userError "integral membership process shape changed")
  unless statements.contains (.assign false "proof_result" membership) do
    throw (IO.userError "membership certificate differs from extracted source")
  unless runSelfCheck design 4096 == Res.ok [
      "signed 1 1 1", "mixed 0 0 0", "context 1 1", "wild 1 x 1",
      "unknown x x x", "dollar 1 0 1", "reverse 0 x", "bounds 0 x x",
      "cells 1 0 0", "enum 1 1", "dominance 1", "nested 1"] do
    throw (IO.userError "integral membership fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.inside.proof
