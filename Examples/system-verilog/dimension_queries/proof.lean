import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dimensionQueries.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/dimension_queries/dimension_queries.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dimension-query fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dimension-query self-check disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dimensionQueries.proof
