import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringNullQueryObservations.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_null_query_observations/string_null_query_observations.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-null-query-observations fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-null-query-observations fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringNullQueryObservations.proof
