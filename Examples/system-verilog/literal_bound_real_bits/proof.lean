import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.literalBoundRealBits.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/literal_bound_real_bits/literal_bound_real_bits.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "literal-bound-real-bits fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "literal-bound-real-bits fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.literalBoundRealBits.proof
