import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicArrayReinitialization.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/dynamic_array_reinitialization/dynamic_array_reinitialization.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dynamic-array-reinitialization fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dynamic-array-reinitialization fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicArrayReinitialization.proof
