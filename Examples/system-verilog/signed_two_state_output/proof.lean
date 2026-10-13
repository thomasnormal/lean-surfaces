import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.signedTwoStateOutput.proof

open LeanModels.Sv
open LeanModels.Sv.SelfCheck

set_option autoImplicit false

theorem signed_two_state_starts_zero (width : Nat) : initDecls 1
    ([{ name := "a", width := width, isOutput := true, isSigned := true, twoState := true }] : List SDecl) [] =
      .ok [("a", LVec.replicate width .l0)] := rfl

#print axioms signed_two_state_starts_zero

def signedTwoStateOutputReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/signed_two_state_output/signed_two_state_output.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "signed two-state output fixture failed to load")
  let some port := design.decls[0]?
    | throw (IO.userError "signed two-state output declaration missing")
  unless port.isOutput && port.isSigned && port.twoState && port.width == 4 do
    throw (IO.userError "signed two-state output metadata was not retained")
  unless runSelfCheck design 4096 == Res.ok ["PASS"] do
    throw (IO.userError "signed two-state output behavior disagrees")

#eval signedTwoStateOutputReceipt

end Examples.systemVerilog.signedTwoStateOutput.proof
