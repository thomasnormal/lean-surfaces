import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringQueryObservations.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_query_observations/string_query_observations.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-query-observations fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-query-observations fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringQueryObservations.proof
