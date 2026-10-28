import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringTypenameAssignment.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_typename_assignment/string_typename_assignment.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-typename-assignment fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-typename-assignment fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringTypenameAssignment.proof
