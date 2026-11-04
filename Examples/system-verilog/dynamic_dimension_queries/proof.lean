import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicDimensionQueries.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/dynamic_dimension_queries/dynamic_dimension_queries.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dynamic-dimension-query fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dynamic-dimension-query self-check disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicDimensionQueries.proof
