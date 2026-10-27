import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.timeformatNamedHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/timeformat_named_history/timeformat_named_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "timeformat-named-history fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "timeformat-named-history fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.timeformatNamedHistory.proof
