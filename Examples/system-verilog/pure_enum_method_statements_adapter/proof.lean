import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.pureEnumMethodStatementsAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/pure_enum_method_statements_adapter/pure_enum_method_statements_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "pure enum method adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "pure enum method adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.pureEnumMethodStatementsAdapter.proof
