import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.qInitializeDuplicateStatus.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/q_initialize_duplicate_status/q_initialize_duplicate_status.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "duplicate queue-ID fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "duplicate queue-ID fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.qInitializeDuplicateStatus.proof
