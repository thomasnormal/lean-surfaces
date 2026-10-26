import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringIndex.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_index/string_index.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-index fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-index fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringIndex.proof
