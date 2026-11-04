import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.queueLiteralThenEmptyConcat.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/queue_literal_then_empty_concat/queue_literal_then_empty_concat.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "queue history fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "queue history fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.queueLiteralThenEmptyConcat.proof
