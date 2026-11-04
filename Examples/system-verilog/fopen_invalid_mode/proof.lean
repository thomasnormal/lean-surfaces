import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fopenInvalidMode.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/fopen_invalid_mode/fopen_invalid_mode.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fopen-invalid-mode fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "fopen-invalid-mode fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fopenInvalidMode.proof
