import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocNextPrevHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/assoc_next_prev_history/assoc_next_prev_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "associative next-prev fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 ==
      .ok ["PASS1", "PASS2", "PASS3", "PASS4", "PASS5"] do
    throw (IO.userError "associative next-prev fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocNextPrevHistory.proof
