import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocSystemBoundsHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/assoc_system_bounds_history/assoc_system_bounds_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "associative system-bounds fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 ==
      .ok ["PASS1", "PASS2"] do
    throw (IO.userError "associative system-bounds fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocSystemBoundsHistory.proof
