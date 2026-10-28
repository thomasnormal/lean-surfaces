import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocCompoundHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/assoc_compound_history/assoc_compound_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "associative compound fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 ==
      .ok ["PASS1", "PASS2"] do
    throw (IO.userError "associative compound fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocCompoundHistory.proof
