import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.arrayReductionStatements.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/array_reduction_statements/array_reduction_statements.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "array-reduction-statements fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "array-reduction-statements fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.arrayReductionStatements.proof
