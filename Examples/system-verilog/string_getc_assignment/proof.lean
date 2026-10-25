import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringGetcAssignment.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_getc_assignment/string_getc_assignment.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-getc-assignment fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-getc-assignment fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringGetcAssignment.proof
