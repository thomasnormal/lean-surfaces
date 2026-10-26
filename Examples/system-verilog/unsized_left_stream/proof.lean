import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.unsizedLeftStream.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/unsized_left_stream/unsized_left_stream.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unsized-left-stream fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "unsized-left-stream fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.unsizedLeftStream.proof
