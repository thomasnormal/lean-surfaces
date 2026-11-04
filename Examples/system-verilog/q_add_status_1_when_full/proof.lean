import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.qAddStatus1WhenFull.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/q_add_status_1_when_full/q_add_status_1_when_full.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "full queue-add fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "full queue-add fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.qAddStatus1WhenFull.proof
