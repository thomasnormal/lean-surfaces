import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.structArrayFieldWindows.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/struct_array_field_windows/struct_array_field_windows.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "struct-array-field-windows fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "struct-array-field-windows fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.structArrayFieldWindows.proof
