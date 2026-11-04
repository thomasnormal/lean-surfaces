import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedArrayNestedConditionalSelfAlias.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/fixed_array_nested_conditional_self_alias/fixed_array_nested_conditional_self_alias.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "nested fixed-array conditional self-alias fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "nested fixed-array conditional self-alias fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedArrayNestedConditionalSelfAlias.proof
