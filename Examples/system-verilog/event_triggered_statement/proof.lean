import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.eventTriggeredStatement.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/event_triggered_statement/event_triggered_statement.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "event-triggered-statement fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "event-triggered-statement fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.eventTriggeredStatement.proof
