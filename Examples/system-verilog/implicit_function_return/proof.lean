import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.implicitFunctionReturn.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/implicit_function_return/implicit_function_return.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "implicit-function-return fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS", "PASS2"] do
    throw (IO.userError "implicit-function-return fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.implicitFunctionReturn.proof
