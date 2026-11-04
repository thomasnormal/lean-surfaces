import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedArrayStructPattern.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/fixed_array_struct_pattern/fixed_array_struct_pattern.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fixed-array-struct-pattern fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "fixed-array-struct-pattern fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedArrayStructPattern.proof
