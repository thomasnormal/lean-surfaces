import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.distUniformArrayTarget.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/dist_uniform_array_target/dist_uniform_array_target.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dist_uniform array fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "dist_uniform array fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.distUniformArrayTarget.proof
