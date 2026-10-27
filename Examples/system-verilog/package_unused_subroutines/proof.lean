import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.packageUnusedSubroutines.proof

open LeanModels.Sv

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/package_unused_subroutines/package_unused_subroutines.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "package-unused-subroutines fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "package-unused-subroutines fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.packageUnusedSubroutines.proof
