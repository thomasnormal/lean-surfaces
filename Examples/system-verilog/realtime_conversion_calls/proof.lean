import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.realtimeConversionCalls.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/realtime_conversion_calls/realtime_conversion_calls.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "realtime-conversion-calls fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "realtime-conversion-calls fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.realtimeConversionCalls.proof
