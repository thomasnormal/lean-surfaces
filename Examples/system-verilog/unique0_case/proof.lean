import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.unique0Case.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/unique0_case/unique0_case.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unique0-case fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "unique0-case fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.unique0Case.proof
