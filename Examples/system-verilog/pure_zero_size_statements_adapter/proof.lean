import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.pureZeroSizeStatementsAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/pure_zero_size_statements_adapter/pure_zero_size_statements_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "pure zero-size adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "pure zero-size adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.pureZeroSizeStatementsAdapter.proof
