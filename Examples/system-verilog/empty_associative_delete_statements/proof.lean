import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.emptyAssociativeDeleteStatements.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/empty_associative_delete_statements/empty_associative_delete_statements.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "empty-associative-delete fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "empty-associative-delete fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.emptyAssociativeDeleteStatements.proof
