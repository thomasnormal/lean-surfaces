import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedArrayStringInitializer.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/fixed_array_string_initializer/fixed_array_string_initializer.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fixed-array-string initializer fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "fixed-array-string initializer self-check disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedArrayStringInitializer.proof
