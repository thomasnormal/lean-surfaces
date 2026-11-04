import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.mixedDimensionQueries.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/mixed_dimension_queries/mixed_dimension_queries.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "mixed-dimension-query fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "mixed-dimension-query self-check disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.mixedDimensionQueries.proof
