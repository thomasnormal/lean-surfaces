import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.invalidPackedDimensionDecl.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/invalid_packed_dimension_decl/invalid_packed_dimension_decl.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "invalid packed-dimension declaration fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "invalid packed-dimension declaration fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.invalidPackedDimensionDecl.proof
