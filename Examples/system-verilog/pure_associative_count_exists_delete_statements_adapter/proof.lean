import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.pureAssociativeCountExistsDeleteStatementsAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/pure_associative_count_exists_delete_statements_adapter/pure_associative_count_exists_delete_statements_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "pure associative count/exists/delete adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "pure associative count/exists/delete adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.pureAssociativeCountExistsDeleteStatementsAdapter.proof
