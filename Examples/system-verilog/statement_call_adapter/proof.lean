import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.statementCallAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/statement_call_adapter/statement_call_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "statement-call adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "statement-call adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.statementCallAdapter.proof
