import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.literalFunctionNamedHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/literal_function_named_history/literal_function_named_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "literal-function-named-history fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS", "PASS"] do
    throw (IO.userError "literal-function-named-history fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.literalFunctionNamedHistory.proof
