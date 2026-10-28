import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocEndpointStatementHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/assoc_endpoint_statement_history/assoc_endpoint_statement_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "associative-endpoint-statement fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS", "PASS2", "PASS3"] do
    throw (IO.userError "associative-endpoint-statement fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocEndpointStatementHistory.proof
