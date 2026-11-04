import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.packedArrayDynamicPartSelect.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/packed_array_dynamic_part_select/packed_array_dynamic_part_select.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "packed-array-dynamic-part-select fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "packed-array-dynamic-part-select fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.packedArrayDynamicPartSelect.proof
