import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicArrayResizeCopy.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/dynamic_array_resize_copy/dynamic_array_resize_copy.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dynamic-array resize-copy fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dynamic-array resize-copy fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicArrayResizeCopy.proof
