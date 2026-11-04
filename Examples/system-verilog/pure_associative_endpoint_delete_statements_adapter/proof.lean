import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.pureAssociativeEndpointDeleteStatementsAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/pure_associative_endpoint_delete_statements_adapter/pure_associative_endpoint_delete_statements_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "pure associative endpoint/delete adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS", "PASS2", "PASS3"] do
    throw (IO.userError "pure associative endpoint/delete adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.pureAssociativeEndpointDeleteStatementsAdapter.proof
