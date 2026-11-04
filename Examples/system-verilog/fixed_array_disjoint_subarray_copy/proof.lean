import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedArrayDisjointSubarrayCopy.proof

open LeanModels.Sv

set_option autoImplicit false


def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/fixed_array_disjoint_subarray_copy/fixed_array_disjoint_subarray_copy.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "disjoint-subarray fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "disjoint-subarray fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedArrayDisjointSubarrayCopy.proof
