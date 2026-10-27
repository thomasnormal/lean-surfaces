import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.qExamStatCode3MaxLengthV3.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/q_exam_stat_code_3_max_length_v3/q_exam_stat_code_3_max_length_v3.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "queue-exam stat-code-3 fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "queue-exam stat-code-3 fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.qExamStatCode3MaxLengthV3.proof
