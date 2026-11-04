import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assertcontrolTasksAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/assertcontrol_tasks_adapter/assertcontrol_tasks_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "assertcontrol tasks adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "assertcontrol tasks adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assertcontrolTasksAdapter.proof
