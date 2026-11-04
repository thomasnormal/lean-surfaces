import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.qAddStatus0.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/q_add_status_0/q_add_status_0.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "queue-add status-0 fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "queue-add status-0 fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.qAddStatus0.proof
