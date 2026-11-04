import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.unpackedCompare.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/unpacked_compare/unpacked_compare.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unpacked-compare fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "unpacked-compare fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.unpackedCompare.proof
