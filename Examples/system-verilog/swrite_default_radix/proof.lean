import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.swriteDefaultRadix.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/swrite_default_radix/swrite_default_radix.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "swrite-default-radix fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "swrite-default-radix fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.swriteDefaultRadix.proof
