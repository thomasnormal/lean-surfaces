import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringQueryStatement.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_query_statement/string_query_statement.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-query-statement fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-query-statement fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringQueryStatement.proof
