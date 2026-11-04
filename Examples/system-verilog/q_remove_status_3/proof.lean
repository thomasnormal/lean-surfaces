import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.qRemoveStatus3.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/q_remove_status_3/q_remove_status_3.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "empty queue fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "empty queue fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.qRemoveStatus3.proof
