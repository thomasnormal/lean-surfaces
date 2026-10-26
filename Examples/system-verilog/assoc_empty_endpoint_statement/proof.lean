import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocEmptyEndpointStatement.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/assoc_empty_endpoint_statement/assoc_empty_endpoint_statement.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "assoc-empty-endpoint-statement fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "assoc-empty-endpoint-statement fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocEmptyEndpointStatement.proof
