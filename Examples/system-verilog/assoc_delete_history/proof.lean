import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocDeleteHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/assoc_delete_history/assoc_delete_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "associative-delete-history fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS", "PASS2", "PASS3"] do
    throw (IO.userError "associative-delete-history fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocDeleteHistory.proof
