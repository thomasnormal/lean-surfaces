import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.nestedDynamicArrayTarget.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/nested_dynamic_array_target/nested_dynamic_array_target.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "nested-dynamic-array-target fixture failed to load")
  unless SelfCheck.runSelfCheck design 16384 == .ok ["PASS"] do
    throw (IO.userError "nested-dynamic-array-target fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.nestedDynamicArrayTarget.proof
