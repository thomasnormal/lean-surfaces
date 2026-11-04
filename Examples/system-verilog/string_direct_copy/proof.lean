import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.stringDirectCopy.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/string_direct_copy/string_direct_copy.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "string-direct-copy fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "string-direct-copy fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.stringDirectCopy.proof
