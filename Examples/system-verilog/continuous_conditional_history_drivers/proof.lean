import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.continuousConditionalHistoryDrivers.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/continuous_conditional_history_drivers/continuous_conditional_history_drivers.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "continuous-conditional-history-drivers fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "continuous-conditional-history-drivers fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.continuousConditionalHistoryDrivers.proof
