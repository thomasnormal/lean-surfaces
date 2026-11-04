import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedArrayDynamicPackedSlice.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/fixed_array_dynamic_packed_slice/fixed_array_dynamic_packed_slice.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fixed-array-dynamic-packed-slice fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "fixed-array-dynamic-packed-slice fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedArrayDynamicPackedSlice.proof
