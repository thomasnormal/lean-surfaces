import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.invalidPackedDimensionLiteral.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/invalid_packed_dimension_literal/invalid_packed_dimension_literal.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "literal invalid packed-dimension fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "literal invalid packed-dimension fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.invalidPackedDimensionLiteral.proof
