import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedArrayDeclAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/fixed_array_decl_adapter/fixed_array_decl_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fixed array declaration adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "fixed array declaration adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedArrayDeclAdapter.proof
