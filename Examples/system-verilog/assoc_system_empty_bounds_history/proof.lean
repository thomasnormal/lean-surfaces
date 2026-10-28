import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocSystemEmptyBoundsHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/assoc_system_empty_bounds_history/assoc_system_empty_bounds_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "empty associative bounds fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "empty associative bounds fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocSystemEmptyBoundsHistory.proof
