import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.qRemoveStatus2.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/q_remove_status_2/q_remove_status_2.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "undefined queue-ID fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "undefined queue-ID fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.qRemoveStatus2.proof
