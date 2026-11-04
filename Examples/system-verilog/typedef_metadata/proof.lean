import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.typedefMetadata.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/typedef_metadata/typedef_metadata.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "typedef metadata fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "typedef metadata fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.typedefMetadata.proof
