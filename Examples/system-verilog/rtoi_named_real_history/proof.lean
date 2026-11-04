import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.rtoiNamedRealHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/rtoi_named_real_history/rtoi_named_real_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "rtoi-named-real-history fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "rtoi-named-real-history fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.rtoiNamedRealHistory.proof
