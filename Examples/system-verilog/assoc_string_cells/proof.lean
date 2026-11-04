import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocStringCells.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/assoc_string_cells/assoc_string_cells.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "associative string-cell fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "associative string-cell fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocStringCells.proof
