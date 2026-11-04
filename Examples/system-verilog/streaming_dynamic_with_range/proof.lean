import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.streamingDynamicWithRange.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/streaming_dynamic_with_range/streaming_dynamic_with_range.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "streaming-dynamic-with-range fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "streaming-dynamic-with-range fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.streamingDynamicWithRange.proof
