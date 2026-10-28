import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.floatingIntegralWrite.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/floating_integral_write/floating_integral_write.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "floating-integral-write fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "floating-integral-write fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.floatingIntegralWrite.proof
