import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.invalidDimensionAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/invalid_dimension_adapter/invalid_dimension_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "invalid dimension adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "invalid dimension adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.invalidDimensionAdapter.proof
