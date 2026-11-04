import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.packedArrayDynamicIndex.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/packed_array_dynamic_index/packed_array_dynamic_index.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "packed-array-dynamic-index fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "packed-array-dynamic-index fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.packedArrayDynamicIndex.proof
