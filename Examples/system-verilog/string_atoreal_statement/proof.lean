import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringAtorealStatement.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_atoreal_statement/string_atoreal_statement.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-atoreal-statement fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-atoreal-statement fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringAtorealStatement.proof
