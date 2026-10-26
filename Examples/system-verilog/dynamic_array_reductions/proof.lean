import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicArrayReductions.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/dynamic_array_reductions/dynamic_array_reductions.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dynamic-array-reductions fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dynamic-array-reductions fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicArrayReductions.proof
