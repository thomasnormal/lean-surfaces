import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dimensionQueryStatements.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/dimension_query_statements/dimension_query_statements.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dimension-query-statements fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dimension-query-statements fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dimensionQueryStatements.proof
