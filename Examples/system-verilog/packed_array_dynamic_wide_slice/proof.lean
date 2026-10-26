import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.packedArrayDynamicWideSlice.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/packed_array_dynamic_wide_slice/packed_array_dynamic_wide_slice.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "packed-array-dynamic-wide-slice fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "packed-array-dynamic-wide-slice fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.packedArrayDynamicWideSlice.proof
