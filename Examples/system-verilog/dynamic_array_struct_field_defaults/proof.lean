import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicArrayStructFieldDefaults.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/dynamic_array_struct_field_defaults/dynamic_array_struct_field_defaults.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dynamic-array-struct-field-defaults fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "dynamic-array-struct-field-defaults fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicArrayStructFieldDefaults.proof
