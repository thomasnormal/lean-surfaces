import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.zeroSizeStatement.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/zero_size_statement/zero_size_statement.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "zero-size-statement fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "zero-size-statement fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.zeroSizeStatement.proof
