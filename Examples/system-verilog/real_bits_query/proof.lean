import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.realBitsQuery.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/real_bits_query/real_bits_query.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "real-bits-query fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "real-bits-query fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.realBitsQuery.proof
