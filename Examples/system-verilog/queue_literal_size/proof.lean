import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.queueLiteralSize.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/queue_literal_size/queue_literal_size.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "literal-queue-size fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "literal-queue-size fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.queueLiteralSize.proof
