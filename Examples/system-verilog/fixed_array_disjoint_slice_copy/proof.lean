import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedArrayDisjointSliceCopy.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/fixed_array_disjoint_slice_copy/fixed_array_disjoint_slice_copy.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fixed-array-disjoint-slice-copy fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "fixed-array-disjoint-slice-copy fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedArrayDisjointSliceCopy.proof
