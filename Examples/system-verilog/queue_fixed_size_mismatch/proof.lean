import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.queueFixedSizeMismatch.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/queue_fixed_size_mismatch/queue_fixed_size_mismatch.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "queue-fixed-size-mismatch fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["BEFORE"] do
    throw (IO.userError "queue-fixed-size-mismatch fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.queueFixedSizeMismatch.proof
