import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.distUniformScalar.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/dist_uniform_scalar/dist_uniform_scalar.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dist_uniform scalar fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dist_uniform scalar fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.distUniformScalar.proof
