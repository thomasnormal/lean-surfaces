import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.qFullValueHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/q_full_value_history/q_full_value_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "q_full value-history fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "q_full value-history fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.qFullValueHistory.proof
