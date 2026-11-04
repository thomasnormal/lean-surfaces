import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.timeQueryStatements.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/time_query_statements/time_query_statements.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "time-query-statements fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "time-query-statements fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.timeQueryStatements.proof
