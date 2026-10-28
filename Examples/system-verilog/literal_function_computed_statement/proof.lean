import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.literalFunctionComputedStatement.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/literal_function_computed_statement/literal_function_computed_statement.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "literal-function-computed-statement fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "literal-function-computed-statement fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.literalFunctionComputedStatement.proof
