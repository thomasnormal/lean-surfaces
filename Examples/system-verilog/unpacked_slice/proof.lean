import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.unpackedSlice.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/unpacked_slice/unpacked_slice.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unpacked-slice fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "unpacked-slice fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.unpackedSlice.proof
