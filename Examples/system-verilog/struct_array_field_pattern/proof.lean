import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.structArrayFieldPattern.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/struct_array_field_pattern/struct_array_field_pattern.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "struct-array-field-pattern fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "struct-array-field-pattern fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.structArrayFieldPattern.proof
