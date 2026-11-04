import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicArrayStructDefaults.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/dynamic_array_struct_defaults/dynamic_array_struct_defaults.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dynamic-array-struct-defaults fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "dynamic-array-struct-defaults fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicArrayStructDefaults.proof
