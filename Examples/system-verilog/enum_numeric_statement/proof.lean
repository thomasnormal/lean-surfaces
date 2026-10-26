import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.enumNumericStatement.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/enum_numeric_statement/enum_numeric_statement.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "enum-numeric-statement fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "enum-numeric-statement fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.enumNumericStatement.proof
