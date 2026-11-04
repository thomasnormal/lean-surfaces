import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.eventTriggeredFalse.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/event_triggered_false/event_triggered_false.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "event-triggered-false fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "event-triggered-false fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.eventTriggeredFalse.proof
