import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.bitQueryNamedHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/bit_query_named_history/bit_query_named_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "bit-query-named-history fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "bit-query-named-history fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.bitQueryNamedHistory.proof
