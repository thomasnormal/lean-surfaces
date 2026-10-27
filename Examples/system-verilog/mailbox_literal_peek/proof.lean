import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.mailboxLiteralPeek.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/mailbox_literal_peek/mailbox_literal_peek.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "mailbox-peek fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "mailbox-peek fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.mailboxLiteralPeek.proof
