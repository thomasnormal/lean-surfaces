import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocExistsCells.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/assoc_exists_cells/assoc_exists_cells.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "associative exists fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "associative exists fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocExistsCells.proof
