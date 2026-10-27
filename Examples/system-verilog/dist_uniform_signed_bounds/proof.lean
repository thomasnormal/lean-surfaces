import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.distUniformSignedBounds.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/dist_uniform_signed_bounds/dist_uniform_signed_bounds.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dist_uniform signed-bounds fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dist_uniform signed-bounds fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.distUniformSignedBounds.proof
