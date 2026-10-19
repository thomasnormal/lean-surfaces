import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.unpackedCells.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/unpacked_cells/unpacked_cells.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unpacked-cell fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "unpacked-cell fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.unpackedCells.proof
