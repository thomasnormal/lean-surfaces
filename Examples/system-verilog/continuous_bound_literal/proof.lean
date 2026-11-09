import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.continuousBoundLiteral.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/continuous_bound_literal/continuous_bound_literal.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "continuous-bound-literal fixture failed to load")
  unless match SelfCheck.runSelfCheck design 4096 with
    | .unsupported msg => msg.startsWith "Initial:order:"
    | _ => false do
    throw (IO.userError "continuous_bound_literal fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.continuousBoundLiteral.proof
