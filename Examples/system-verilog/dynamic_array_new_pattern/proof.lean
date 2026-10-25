import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicArrayNewPattern.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/dynamic_array_new_pattern/dynamic_array_new_pattern.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dynamic-array new-pattern fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dynamic-array new-pattern fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicArrayNewPattern.proof
