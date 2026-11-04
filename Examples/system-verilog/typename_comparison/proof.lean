import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.typenameComparison.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/typename_comparison/typename_comparison.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "typename-comparison fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "typename-comparison fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.typenameComparison.proof
