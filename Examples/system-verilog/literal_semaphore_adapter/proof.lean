import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.literalSemaphoreAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/literal_semaphore_adapter/literal_semaphore_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "literal semaphore adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "literal semaphore adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.literalSemaphoreAdapter.proof
