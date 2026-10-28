import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.discardedPureRtoi.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/discarded_pure_rtoi/discarded_pure_rtoi.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "discarded-pure-rtoi fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "discarded-pure-rtoi fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.discardedPureRtoi.proof
