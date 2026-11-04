import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.packageMetadata.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/package_metadata/package_metadata.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "package metadata fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["a5", "PASS"] do
    throw (IO.userError "package metadata fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.packageMetadata.proof
