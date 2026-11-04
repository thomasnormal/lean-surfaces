import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.mailboxParameterizedPackedVector.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/mailbox_parameterized_packed_vector/mailbox_parameterized_packed_vector.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "parameterized-packed-mailbox fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "parameterized-packed-mailbox fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.mailboxParameterizedPackedVector.proof
