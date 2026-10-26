import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.isunboundedStatement.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/isunbounded_statement/isunbounded_statement.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "isunbounded-statement fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "isunbounded-statement fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.isunboundedStatement.proof
