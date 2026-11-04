import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.staticFixedArrayContinuousCopy.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/static_fixed_array_continuous_copy/static_fixed_array_continuous_copy.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "static-fixed-array-continuous-copy fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "static-fixed-array-continuous-copy fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.staticFixedArrayContinuousCopy.proof
