import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.parameterMetadata.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/parameter_metadata/parameter_metadata.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "parameter metadata fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["8", "a", "a5", "PASS"] do
    throw (IO.userError "parameter metadata fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.parameterMetadata.proof
