import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicArrayResizeFixedSource.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/dynamic_array_resize_fixed_source/dynamic_array_resize_fixed_source.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fixed-source dynamic-array fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "fixed-source dynamic-array fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicArrayResizeFixedSource.proof
