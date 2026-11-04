import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringPutcLengthIndex.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_putc_length_index/string_putc_length_index.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-putc-length-index fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-putc-length-index fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringPutcLengthIndex.proof
