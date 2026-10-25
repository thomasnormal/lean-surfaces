import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.semaphoreLiteralPutGet.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/semaphore_literal_put_get/semaphore_literal_put_get.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "semaphore-literal-put-get fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "semaphore-literal-put-get fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.semaphoreLiteralPutGet.proof
