import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.wiredNetResolution.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/wired_net_resolution/wired_net_resolution.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "wired-net fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "wired-net fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.wiredNetResolution.proof
