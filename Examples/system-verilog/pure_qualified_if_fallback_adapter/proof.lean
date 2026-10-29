import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.pureQualifiedIfFallbackAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/pure_qualified_if_fallback_adapter/pure_qualified_if_fallback_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "pure qualified-if fallback adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "pure qualified-if fallback adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.pureQualifiedIfFallbackAdapter.proof
