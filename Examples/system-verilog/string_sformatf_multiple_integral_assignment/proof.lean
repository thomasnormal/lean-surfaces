import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringSformatfMultipleIntegralAssignment.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_sformatf_multiple_integral_assignment/string_sformatf_multiple_integral_assignment.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-sformatf-multiple-integral-assignment fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-sformatf-multiple-integral-assignment fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringSformatfMultipleIntegralAssignment.proof
