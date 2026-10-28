import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocUnsignedEndpointHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/assoc_unsigned_endpoint_history/assoc_unsigned_endpoint_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unsigned associative endpoint fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "unsigned associative endpoint fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocUnsignedEndpointHistory.proof
