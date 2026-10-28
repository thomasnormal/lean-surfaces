import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.pureIntegralRealConversions.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/pure_integral_real_conversions/pure_integral_real_conversions.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "pure-integral-real-conversions fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "pure-integral-real-conversions fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.pureIntegralRealConversions.proof
