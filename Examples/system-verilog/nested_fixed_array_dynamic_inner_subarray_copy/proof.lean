import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.nestedFixedArrayDynamicInnerSubarrayCopy.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/nested_fixed_array_dynamic_inner_subarray_copy/nested_fixed_array_dynamic_inner_subarray_copy.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "nested-fixed-array-dynamic-inner-subarray-copy fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "nested-fixed-array-dynamic-inner-subarray-copy fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.nestedFixedArrayDynamicInnerSubarrayCopy.proof
