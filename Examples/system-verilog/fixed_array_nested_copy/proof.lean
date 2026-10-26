import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedArrayNestedCopy.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/fixed_array_nested_copy/fixed_array_nested_copy.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fixed-array-nested-copy fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "fixed-array-nested-copy fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedArrayNestedCopy.proof
