import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.supplyNet.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/supply_net/supply_net.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "supply-net fixture failed to load")
  unless SelfCheck.runSelfCheck design 16384 == .ok ["PASS"] do
    throw (IO.userError "supply-net fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.supplyNet.proof
