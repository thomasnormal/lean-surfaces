import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.structDeclAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/struct_decl_adapter/struct_decl_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "struct declaration adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "struct declaration adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.structDeclAdapter.proof
