import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fopenInvalidModeStatement.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/fopen_invalid_mode_statement/fopen_invalid_mode_statement.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fopen-invalid-mode-statement fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "fopen-invalid-mode-statement fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fopenInvalidModeStatement.proof
