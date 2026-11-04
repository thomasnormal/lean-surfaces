import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringCompareObservations.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_compare_observations/string_compare_observations.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-compare-observations fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-compare-observations fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringCompareObservations.proof
