import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.bitsDiscarded.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/bits_discarded/bits_discarded.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "bits-discarded fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "bits-discarded fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.bitsDiscarded.proof
