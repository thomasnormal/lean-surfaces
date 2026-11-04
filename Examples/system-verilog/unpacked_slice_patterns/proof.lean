import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.unpackedSlicePatterns.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/unpacked_slice_patterns/unpacked_slice_patterns.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unpacked-slice-patterns fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "unpacked-slice-patterns fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.unpackedSlicePatterns.proof
