import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.foreachNested.proof

open LeanModels.Sv

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/foreach_nested/foreach_nested.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "foreach-nested fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 ==
      .ok ["sum=21"] do
    throw (IO.userError "foreach-nested fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.foreachNested.proof
