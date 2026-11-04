import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.packedStruct.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/packed_struct/packed_struct.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "packed-struct fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "packed-struct fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.packedStruct.proof
