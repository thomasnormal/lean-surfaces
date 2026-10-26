import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocEmptyQueryStatement.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/assoc_empty_query_statement/assoc_empty_query_statement.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "assoc-empty-query-statement fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "assoc-empty-query-statement fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocEmptyQueryStatement.proof
