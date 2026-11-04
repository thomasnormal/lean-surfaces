import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.systemNull.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/system_null/system_null.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "system-null fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "system-null fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.systemNull.proof
