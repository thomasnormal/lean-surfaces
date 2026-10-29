import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.pureRealConversionStatementsAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/pure_real_conversion_statements_adapter/pure_real_conversion_statements_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "pure real conversion adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "pure real conversion adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.pureRealConversionStatementsAdapter.proof
