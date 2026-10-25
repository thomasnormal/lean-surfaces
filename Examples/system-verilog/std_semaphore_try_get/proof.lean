import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stdSemaphoreTryGet.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/std_semaphore_try_get/std_semaphore_try_get.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "std-semaphore-try-get fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "std-semaphore-try-get fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stdSemaphoreTryGet.proof
