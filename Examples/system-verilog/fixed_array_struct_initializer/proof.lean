import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedArrayStructInitializer.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/fixed_array_struct_initializer/fixed_array_struct_initializer.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fixed-array-struct initializer fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "fixed-array-struct initializer self-check disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedArrayStructInitializer.proof
