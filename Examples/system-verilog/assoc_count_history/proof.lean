import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocCountHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/assoc_count_history/assoc_count_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "associative-count-history fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "associative-count-history fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocCountHistory.proof
