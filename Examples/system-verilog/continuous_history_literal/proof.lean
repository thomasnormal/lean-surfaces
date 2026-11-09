import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.continuousHistoryLiteral.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/continuous_history_literal/continuous_history_literal.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "continuous-history-literal fixture failed to load")
  unless match SelfCheck.runSelfCheck design 4096 with
    | .unsupported msg => msg.startsWith "Initial:order:"
    | _ => false do
    throw (IO.userError "continuous_history_literal fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.continuousHistoryLiteral.proof
