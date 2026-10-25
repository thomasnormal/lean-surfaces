import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicArrayConcatSubarrays.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/dynamic_array_concat_subarrays/dynamic_array_concat_subarrays.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dynamic-array-concat-subarrays fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dynamic-array-concat-subarrays fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicArrayConcatSubarrays.proof
