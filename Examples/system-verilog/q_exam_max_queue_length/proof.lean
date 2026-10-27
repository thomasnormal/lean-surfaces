import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.qExamMaxQueueLength.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/q_exam_max_queue_length/q_exam_max_queue_length.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "queue-exam maximum-length fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "queue-exam maximum-length fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.qExamMaxQueueLength.proof
