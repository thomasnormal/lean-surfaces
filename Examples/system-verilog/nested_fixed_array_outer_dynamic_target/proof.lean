import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.nestedFixedArrayOuterDynamicTarget.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/nested_fixed_array_outer_dynamic_target/nested_fixed_array_outer_dynamic_target.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "nested-fixed-array-outer-dynamic-target fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "nested-fixed-array-outer-dynamic-target fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.nestedFixedArrayOuterDynamicTarget.proof
