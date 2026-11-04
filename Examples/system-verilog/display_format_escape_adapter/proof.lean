import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.displayFormatEscapeAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/display_format_escape_adapter/display_format_escape_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "display format escape fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["octal S", "PASS"] do
    throw (IO.userError "display format escape fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.displayFormatEscapeAdapter.proof
