import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.packedArrayMultidim.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/packed_array_multidim/packed_array_multidim.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "packed-array fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "packed-array fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.packedArrayMultidim.proof
