import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.wiredNet.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/wired_net/wired_net.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "wired-net fixture failed to load")
  unless SelfCheck.runSelfCheck design 16384 == .ok ["PASS"] do
    throw (IO.userError "wired-net fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.wiredNet.proof
