import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.queueFixedArrayCopy.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/queue_fixed_array_copy/queue_fixed_array_copy.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "queue-fixed-array fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "queue-fixed-array fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.queueFixedArrayCopy.proof
