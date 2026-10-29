import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.defaultDisplayFormat.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/default_display_format/default_display_format.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "default-display-format fixture failed to load")
  unless SelfCheck.runSelfCheck design 16384 == .ok ["175", "175", "hello"] do
    throw (IO.userError "default-display-format fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.defaultDisplayFormat.proof
