import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.mailboxTypeMismatch.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/mailbox_type_mismatch/mailbox_type_mismatch.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "mailbox-type-mismatch fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "mailbox-type-mismatch fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.mailboxTypeMismatch.proof
