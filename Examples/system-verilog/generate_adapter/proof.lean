import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.generateAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/generate_adapter/generate_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "generate adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "generate adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.generateAdapter.proof
