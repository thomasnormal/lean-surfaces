import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.sformatfStatement.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/sformatf_statement/sformatf_statement.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "sformatf statement fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "sformatf statement fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.sformatfStatement.proof
