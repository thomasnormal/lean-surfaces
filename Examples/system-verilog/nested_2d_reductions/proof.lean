import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.nested2dReductions.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/nested_2d_reductions/nested_2d_reductions.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "nested-2d-reductions fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "nested-2d-reductions fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.nested2dReductions.proof
