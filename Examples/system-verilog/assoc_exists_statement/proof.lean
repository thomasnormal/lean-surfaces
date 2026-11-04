import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocExistsStatement.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/assoc_exists_statement/assoc_exists_statement.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "associative exists statement fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "associative exists statement fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocExistsStatement.proof
