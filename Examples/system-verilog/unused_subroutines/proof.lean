import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.unusedSubroutines.proof

open LeanModels.Sv

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/unused_subroutines/unused_subroutines.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unused-subroutines fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "unused-subroutines fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.unusedSubroutines.proof
