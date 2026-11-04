import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringPutcHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_putc_history/string_putc_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-putc-history fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-putc-history fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringPutcHistory.proof
