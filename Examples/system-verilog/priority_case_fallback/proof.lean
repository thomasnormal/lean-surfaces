import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.priorityCaseFallback.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/priority_case_fallback/priority_case_fallback.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "priority-case-fallback fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "priority-case-fallback fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.priorityCaseFallback.proof
