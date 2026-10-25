import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.semaphoreDefaultTryGet.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/semaphore_default_try_get/semaphore_default_try_get.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "semaphore-default-try-get fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "semaphore-default-try-get fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.semaphoreDefaultTryGet.proof
