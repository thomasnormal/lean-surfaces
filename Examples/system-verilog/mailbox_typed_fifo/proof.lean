import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.mailboxTypedFifo.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/mailbox_typed_fifo/mailbox_typed_fifo.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "typed-mailbox-fifo fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "typed-mailbox-fifo fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.mailboxTypedFifo.proof
