import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.uniqueCaseComplete.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/unique_case_complete/unique_case_complete.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unique-case fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "unique-case fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.uniqueCaseComplete.proof
