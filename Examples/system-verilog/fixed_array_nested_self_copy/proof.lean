import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedArrayNestedSelfCopy.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/fixed_array_nested_self_copy/fixed_array_nested_self_copy.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "nested fixed-array self-copy fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "nested fixed-array self-copy fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedArrayNestedSelfCopy.proof
