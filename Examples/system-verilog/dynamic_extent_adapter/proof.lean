import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicExtentAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/dynamic_extent_adapter/dynamic_extent_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dynamic extent adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dynamic extent adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicExtentAdapter.proof
