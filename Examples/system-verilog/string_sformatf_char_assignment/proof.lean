import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringSformatfCharAssignment.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_sformatf_char_assignment/string_sformatf_char_assignment.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-sformatf-char-assignment fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-sformatf-char-assignment fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringSformatfCharAssignment.proof
