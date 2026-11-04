import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.semaphoreNegativeTryGet.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/semaphore_negative_try_get/semaphore_negative_try_get.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "negative-semaphore-try-get fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "negative-semaphore-try-get fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.semaphoreNegativeTryGet.proof
