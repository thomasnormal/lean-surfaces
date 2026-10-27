import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.realIntegralCast.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/real_integral_cast/real_integral_cast.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "real-integral-cast fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "real-integral-cast fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.realIntegralCast.proof
