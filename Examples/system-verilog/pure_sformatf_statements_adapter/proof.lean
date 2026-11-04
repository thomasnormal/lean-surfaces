import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.pureSformatfStatementsAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/pure_sformatf_statements_adapter/pure_sformatf_statements_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "pure sformatf adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "pure sformatf adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.pureSformatfStatementsAdapter.proof
