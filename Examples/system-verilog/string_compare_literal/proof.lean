import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringCompareLiteral.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/string_compare_literal/string_compare_literal.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-compare-literal fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-compare-literal fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringCompareLiteral.proof
