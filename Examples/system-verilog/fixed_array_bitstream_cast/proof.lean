import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedArrayBitstreamCast.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/fixed_array_bitstream_cast/fixed_array_bitstream_cast.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fixed-array-bitstream-cast fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "fixed-array-bitstream-cast fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedArrayBitstreamCast.proof
