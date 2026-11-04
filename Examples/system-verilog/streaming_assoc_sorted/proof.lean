import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.streamingAssocSorted.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/streaming_assoc_sorted/streaming_assoc_sorted.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "sorted-associative-stream fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "sorted-associative-stream fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.streamingAssocSorted.proof
