import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.bitsFixedExpr.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/bits_fixed_expr/bits_fixed_expr.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fixed-bits fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "fixed-bits fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.bitsFixedExpr.proof
