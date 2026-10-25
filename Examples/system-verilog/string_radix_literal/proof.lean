import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringRadixLiteral.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/string_radix_literal/string_radix_literal.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-radix-literal fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-radix-literal fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringRadixLiteral.proof
