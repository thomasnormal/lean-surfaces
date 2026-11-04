import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.clog2Statement.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/clog2_statement/clog2_statement.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "clog2-statement fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "clog2-statement fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.clog2Statement.proof
