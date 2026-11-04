import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.severityDefaultFormat.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/severity_default_format/severity_default_format.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "severity-default-format fixture failed to load")
  unless SelfCheck.runSelfCheck design 16384 == .ok ["PASS"] do
    throw (IO.userError "severity-default-format fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.severityDefaultFormat.proof
