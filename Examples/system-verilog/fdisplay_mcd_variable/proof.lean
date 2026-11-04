import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fdisplayMcdVariable.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/fdisplay_mcd_variable/fdisplay_mcd_variable.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fdisplay-mcd-variable fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS via MCD bit 0"] do
    throw (IO.userError "fdisplay-mcd-variable fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fdisplayMcdVariable.proof
