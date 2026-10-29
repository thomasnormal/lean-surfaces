import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.twoStateNet.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/two_state_net/two_state_net.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "two-state-net fixture failed to load")
  unless SelfCheck.runSelfCheck design 16384 == .ok ["PASS"] do
    throw (IO.userError "two-state-net fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.twoStateNet.proof
