import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringConcatComparison.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_concat_comparison/string_concat_comparison.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-concat-comparison fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["Hello World"] do
    throw (IO.userError "string-concat-comparison fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringConcatComparison.proof
