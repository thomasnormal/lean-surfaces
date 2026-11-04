import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicArrayLiteralSize.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/dynamic_array_literal_size/dynamic_array_literal_size.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dynamic-array-literal-size fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dynamic-array-literal-size fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicArrayLiteralSize.proof
