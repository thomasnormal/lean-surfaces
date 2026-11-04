import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.qExamCurrentLength.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/q_exam_current_length/q_exam_current_length.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "queue-exam current-length fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "queue-exam current-length fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.qExamCurrentLength.proof
