import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.mailboxModuleInit.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/mailbox_module_init/mailbox_module_init.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "module-mailbox fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "module-mailbox fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.mailboxModuleInit.proof
