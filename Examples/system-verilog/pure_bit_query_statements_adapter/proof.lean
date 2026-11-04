import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.pureBitQueryStatementsAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/pure_bit_query_statements_adapter/pure_bit_query_statements_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "pure bit query adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "pure bit query adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.pureBitQueryStatementsAdapter.proof
