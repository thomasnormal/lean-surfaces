import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.structArrayOrderingWithField.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/struct_array_ordering_with_field/struct_array_ordering_with_field.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "struct-array ordering fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["SORT PASS", "RSORT PASS"] do
    throw (IO.userError "struct-array ordering fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.structArrayOrderingWithField.proof
