import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.pureFloatingMathStatementsAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/pure_floating_math_statements_adapter/pure_floating_math_statements_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "pure floating math adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "pure floating math adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.pureFloatingMathStatementsAdapter.proof
