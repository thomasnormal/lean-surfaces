import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.streamingUnpack.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/streaming_unpack/streaming_unpack.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "streaming-unpack fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "streaming-unpack fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.streamingUnpack.proof
