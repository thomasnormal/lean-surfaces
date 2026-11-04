import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.streamingWithPreviousExtent.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/streaming_with_previous_extent/streaming_with_previous_extent.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "streaming-with-previous-extent fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "streaming-with-previous-extent fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.streamingWithPreviousExtent.proof
