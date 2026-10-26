import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.structArrayFieldDefault.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/struct_array_field_default/struct_array_field_default.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "struct-array-field-default fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["DEFAULT PASS", "KEYED PASS"] do
    throw (IO.userError "struct-array-field-default fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.structArrayFieldDefault.proof
