import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.userNettype.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/user_nettype/user_nettype.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "user-nettype fixture failed to load")
  unless SelfCheck.runSelfCheck design 16384 == .ok ["PASS"] do
    throw (IO.userError "user-nettype fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.userNettype.proof
