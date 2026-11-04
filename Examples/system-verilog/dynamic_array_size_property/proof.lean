import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicArraySizeProperty.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/dynamic_array_size_property/dynamic_array_size_property.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dynamic-array-size-property fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dynamic-array-size-property fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicArraySizeProperty.proof
