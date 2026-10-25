import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.emptyDynamicBits.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/empty_dynamic_bits/empty_dynamic_bits.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "empty-dynamic-bits fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "empty-dynamic-bits fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.emptyDynamicBits.proof
