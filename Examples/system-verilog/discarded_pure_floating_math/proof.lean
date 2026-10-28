import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.discardedPureFloatingMath.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/discarded_pure_floating_math/discarded_pure_floating_math.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "discarded-pure-floating-math fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "discarded-pure-floating-math fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.discardedPureFloatingMath.proof
