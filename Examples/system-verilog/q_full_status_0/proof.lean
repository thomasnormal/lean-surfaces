import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.qFullStatus0.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/q_full_status_0/q_full_status_0.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "queue-full status-0 fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "queue-full status-0 fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.qFullStatus0.proof
