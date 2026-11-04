import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.distUniformVariableBounds.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/dist_uniform_variable_bounds/dist_uniform_variable_bounds.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dist_uniform variable-bounds fixture failed to load")
  unless SelfCheck.runSelfCheck design 65536 == .ok ["PASS"] do
    throw (IO.userError "dist_uniform variable-bounds fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.distUniformVariableBounds.proof
