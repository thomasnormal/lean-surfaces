import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.unpackedDynamic.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/unpacked_dynamic/unpacked_dynamic.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unpacked-dynamic fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS1", "PASS2", "PASS3"] do
    throw (IO.userError "unpacked-dynamic fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.unpackedDynamic.proof
