import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicArrayIndexReduction.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/dynamic_array_index_reduction/dynamic_array_index_reduction.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dynamic-array-index-reduction fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dynamic-array-index-reduction fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicArrayIndexReduction.proof
