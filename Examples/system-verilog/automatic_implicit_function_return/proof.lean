import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.automaticImplicitFunctionReturn.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/automatic_implicit_function_return/automatic_implicit_function_return.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "automatic-implicit-function-return fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS", "PASS2"] do
    throw (IO.userError "automatic-implicit-function-return fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.automaticImplicitFunctionReturn.proof
