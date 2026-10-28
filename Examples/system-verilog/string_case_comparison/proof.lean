import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringCaseComparison.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_case_comparison/string_case_comparison.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-case comparison fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-case comparison fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringCaseComparison.proof
