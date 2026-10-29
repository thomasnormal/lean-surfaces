import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.forwardTypedefMetadata.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/forward_typedef_metadata/forward_typedef_metadata.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "forward typedef fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["42", "PASS"] do
    throw (IO.userError "forward typedef fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.forwardTypedefMetadata.proof
