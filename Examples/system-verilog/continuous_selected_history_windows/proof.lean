import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.continuousSelectedHistoryWindows.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/continuous_selected_history_windows/continuous_selected_history_windows.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "continuous-selected-history-windows fixture failed to load")
  unless match SelfCheck.runSelfCheck design 4096 with
    | .unsupported msg => msg.startsWith "Initial:order:"
    | _ => false do
    throw (IO.userError "continuous_selected_history_windows fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.continuousSelectedHistoryWindows.proof
