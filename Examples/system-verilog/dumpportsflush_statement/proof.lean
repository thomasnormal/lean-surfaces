import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.dumpportsflushStatement.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/dumpportsflush_statement/dumpportsflush_statement.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "dumpportsflush fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "dumpportsflush fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.dumpportsflushStatement.proof
