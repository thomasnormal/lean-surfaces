import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.mailboxEmptyTry.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/mailbox_empty_try/mailbox_empty_try.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "mailbox-empty-try fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "mailbox-empty-try fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.mailboxEmptyTry.proof
