import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicArrayFixedSubarrays.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/dynamic_array_fixed_subarrays/dynamic_array_fixed_subarrays.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dynamic-array fixed-subarray fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dynamic-array fixed-subarray fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicArrayFixedSubarrays.proof
