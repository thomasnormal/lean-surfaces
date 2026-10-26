import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringTransformStatements.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_transform_statements/string_transform_statements.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-transform-statements fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-transform-statements fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringTransformStatements.proof
