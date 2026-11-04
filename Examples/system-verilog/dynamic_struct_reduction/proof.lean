import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicStructReduction.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/dynamic_struct_reduction/dynamic_struct_reduction.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dynamic-struct-reduction fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dynamic-struct-reduction fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicStructReduction.proof
