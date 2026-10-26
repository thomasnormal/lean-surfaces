import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.emptyArrayReductions.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/empty_array_reductions/empty_array_reductions.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "empty-array-reductions fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "empty-array-reductions fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.emptyArrayReductions.proof
