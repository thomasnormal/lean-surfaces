import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringAtoiLiteral.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/string_atoi_literal/string_atoi_literal.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-atoi-literal fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-atoi-literal fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringAtoiLiteral.proof
