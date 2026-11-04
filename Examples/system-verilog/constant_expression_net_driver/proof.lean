import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.constantExpressionNetDriver.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/constant_expression_net_driver/constant_expression_net_driver.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "constant-expression-net-driver fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "constant-expression-net-driver fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.constantExpressionNetDriver.proof
