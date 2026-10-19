import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.unpackedConditional.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/unpacked_conditional/unpacked_conditional.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unpacked-conditional fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS1", "PASS2"] do
    throw (IO.userError "unpacked-conditional fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.unpackedConditional.proof
