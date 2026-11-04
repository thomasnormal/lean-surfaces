import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.discardedPureRealToBits.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/discarded_pure_real_to_bits/discarded_pure_real_to_bits.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "discarded-pure-real-to-bits fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "discarded-pure-real-to-bits fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.discardedPureRealToBits.proof
