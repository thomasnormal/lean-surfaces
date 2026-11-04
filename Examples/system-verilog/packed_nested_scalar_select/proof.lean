import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.packedNestedScalarSelect.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/packed_nested_scalar_select/packed_nested_scalar_select.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "packed-nested-scalar-select fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "packed-nested-scalar-select fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.packedNestedScalarSelect.proof
