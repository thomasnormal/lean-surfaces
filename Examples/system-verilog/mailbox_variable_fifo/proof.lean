import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.mailboxVariableFifo.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/mailbox_variable_fifo/mailbox_variable_fifo.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "variable-mailbox-fifo fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "variable-mailbox-fifo fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.mailboxVariableFifo.proof
