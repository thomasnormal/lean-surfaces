import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dynamicArrayFourState.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/dynamic_array_four_state/dynamic_array_four_state.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "four-state dynamic-array fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "four-state dynamic-array fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dynamicArrayFourState.proof
