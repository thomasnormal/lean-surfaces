import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringQueryLexing.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_query_lexing/string_query_lexing.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-query-lexing fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-query-lexing fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringQueryLexing.proof
