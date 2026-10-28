import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicArrayConcatLiteralFunction.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/dynamic_array_concat_literal_function/dynamic_array_concat_literal_function.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dynamic-array literal-function fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dynamic-array literal-function fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicArrayConcatLiteralFunction.proof
