import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.queueEmptyPopDiscarded.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/queue_empty_pop_discarded/queue_empty_pop_discarded.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "discarded empty-queue-pop fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "discarded empty-queue-pop fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.queueEmptyPopDiscarded.proof
