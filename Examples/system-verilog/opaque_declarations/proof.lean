import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.opaqueDeclarations.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/opaque_declarations/opaque_declarations.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "opaque declaration fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "opaque declaration fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.opaqueDeclarations.proof
