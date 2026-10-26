import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.enumNameStatement.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/enum_name_statement/enum_name_statement.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "enum-name-statement fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "enum-name-statement fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.enumNameStatement.proof
