import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.conditionalStringAssignment.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/conditional_string_assignment/conditional_string_assignment.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "conditional-string-assignment fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "conditional-string-assignment fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.conditionalStringAssignment.proof
