import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.packedRanges.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/packed_ranges/packed_ranges.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "packed-range fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "packed-range fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.packedRanges.proof
