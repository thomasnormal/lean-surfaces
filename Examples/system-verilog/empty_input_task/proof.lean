import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.emptyInputTask.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/empty_input_task/empty_input_task.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "empty-input-task fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "empty-input-task fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.emptyInputTask.proof
