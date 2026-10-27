import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.emptyAggregateDeleteStatements.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/empty_aggregate_delete_statements/empty_aggregate_delete_statements.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "empty-aggregate-delete fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "empty-aggregate-delete fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.emptyAggregateDeleteStatements.proof
