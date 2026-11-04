import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.emptyDynamicDeclAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/empty_dynamic_decl_adapter/empty_dynamic_decl_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "empty dynamic declaration adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "empty dynamic declaration adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.emptyDynamicDeclAdapter.proof
