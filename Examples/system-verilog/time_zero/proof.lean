import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.timeZero.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/time_zero/time_zero.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "time-zero fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "time-zero fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.timeZero.proof
