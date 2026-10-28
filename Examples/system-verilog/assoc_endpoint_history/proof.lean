import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocEndpointHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/assoc_endpoint_history/assoc_endpoint_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "associative-endpoint-history fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS", "PASS5", "PASS2", "PASS3", "PASS4"] do
    throw (IO.userError "associative-endpoint-history fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocEndpointHistory.proof
