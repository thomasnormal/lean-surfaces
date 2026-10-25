import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.mailboxNumLifetime.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/mailbox_num_lifetime/mailbox_num_lifetime.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "mailbox-num-lifetime fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "mailbox-num-lifetime fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.mailboxNumLifetime.proof
