import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.pureFopenInvalidModeStatementsAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/pure_fopen_invalid_mode_statements_adapter/pure_fopen_invalid_mode_statements_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "pure fopen invalid-mode adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "pure fopen invalid-mode adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.pureFopenInvalidModeStatementsAdapter.proof
