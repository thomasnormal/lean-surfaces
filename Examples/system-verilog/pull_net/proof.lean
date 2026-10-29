import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.pullNet.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/pull_net/pull_net.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "pull-net fixture failed to load")
  unless SelfCheck.runSelfCheck design 16384 == .ok ["PASS"] do
    throw (IO.userError "pull-net fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.pullNet.proof
