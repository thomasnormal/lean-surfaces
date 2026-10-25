import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.isunboundedBounded.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/isunbounded_bounded/isunbounded_bounded.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "bounded-isunbounded fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "bounded-isunbounded fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.isunboundedBounded.proof
