import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.mailboxLiteralPutNum.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/mailbox_literal_put_num/mailbox_literal_put_num.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "mailbox-literal-put-num fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "mailbox-literal-put-num fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.mailboxLiteralPutNum.proof
