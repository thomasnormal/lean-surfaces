import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.enumNameComparison.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/enum_name_comparison/enum_name_comparison.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "enum-name comparison fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "enum-name comparison fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.enumNameComparison.proof
