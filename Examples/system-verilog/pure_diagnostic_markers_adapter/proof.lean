import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.pureDiagnosticMarkersAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/pure_diagnostic_markers_adapter/pure_diagnostic_markers_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "pure diagnostic markers adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "pure diagnostic markers adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.pureDiagnosticMarkersAdapter.proof
