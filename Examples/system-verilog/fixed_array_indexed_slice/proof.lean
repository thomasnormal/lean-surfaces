import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedArrayIndexedSlice.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/fixed_array_indexed_slice/fixed_array_indexed_slice.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fixed-array-indexed-slice fixture failed to load")
  unless SelfCheck.runSelfCheck design 16384 == .ok ["PASS"] do
    throw (IO.userError "fixed-array-indexed-slice fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedArrayIndexedSlice.proof
