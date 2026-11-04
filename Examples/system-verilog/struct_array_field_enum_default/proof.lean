import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.structArrayFieldEnumDefault.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/struct_array_field_enum_default/struct_array_field_enum_default.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "struct-array-field-enum-default fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "struct-array-field-enum-default fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.structArrayFieldEnumDefault.proof
