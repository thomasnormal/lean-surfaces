import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.qExamStatCodes.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/q_exam_stat_codes/q_exam_stat_codes.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "named queue-exam fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "named queue-exam fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.qExamStatCodes.proof
