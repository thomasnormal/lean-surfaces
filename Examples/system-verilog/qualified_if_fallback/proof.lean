import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.qualifiedIfFallback.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/qualified_if_fallback/qualified_if_fallback.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "qualified-if-fallback fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "qualified-if-fallback fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.qualifiedIfFallback.proof
