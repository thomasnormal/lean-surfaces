import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.qRemovePayload.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/q_remove_payload/q_remove_payload.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "queue-remove payload fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "queue-remove payload fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.qRemovePayload.proof
