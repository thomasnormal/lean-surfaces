import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.qExamStaticHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/q_exam_static_history/q_exam_static_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "static queue-exam fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "static queue-exam fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.qExamStaticHistory.proof
