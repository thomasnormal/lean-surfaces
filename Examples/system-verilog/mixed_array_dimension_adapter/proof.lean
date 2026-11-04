import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.mixedArrayDimensionAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/mixed_array_dimension_adapter/mixed_array_dimension_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "mixed array adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "mixed array adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.mixedArrayDimensionAdapter.proof
