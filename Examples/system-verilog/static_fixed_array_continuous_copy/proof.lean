import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.staticFixedArrayContinuousCopy.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/static_fixed_array_continuous_copy/static_fixed_array_continuous_copy.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "static-fixed-array-continuous-copy fixture failed to load")
  unless match SelfCheck.runSelfCheck design 4096 with
    | .unsupported msg => msg.startsWith "Initial:order:"
    | _ => false do
    throw (IO.userError "static_fixed_array_continuous_copy fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.staticFixedArrayContinuousCopy.proof
