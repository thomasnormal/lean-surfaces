import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.queueEmptyPopStructDefault.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/queue_empty_pop_struct_default/queue_empty_pop_struct_default.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "empty-queue struct-pop fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "empty-queue struct-pop fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.queueEmptyPopStructDefault.proof
