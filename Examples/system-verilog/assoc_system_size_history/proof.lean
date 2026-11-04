import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocSystemSizeHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/assoc_system_size_history/assoc_system_size_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "associative system-size fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 ==
      .ok ["PASS1", "PASS2", "PASS3"] do
    throw (IO.userError "associative system-size fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocSystemSizeHistory.proof
