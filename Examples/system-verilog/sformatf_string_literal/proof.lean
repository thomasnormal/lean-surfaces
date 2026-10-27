import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.sformatfStringLiteral.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/sformatf_string_literal/sformatf_string_literal.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "sformatf string-literal fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["hello"] do
    throw (IO.userError "sformatf string-literal fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.sformatfStringLiteral.proof
