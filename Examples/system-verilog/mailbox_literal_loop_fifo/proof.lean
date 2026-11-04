import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.mailboxLiteralLoopFifo.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/mailbox_literal_loop_fifo/mailbox_literal_loop_fifo.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "mailbox loop FIFO fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "mailbox loop FIFO fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.mailboxLiteralLoopFifo.proof
