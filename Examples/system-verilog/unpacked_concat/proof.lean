import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.unpackedConcat.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/unpacked_concat/unpacked_concat.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unpacked-concat fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "unpacked-concat fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.unpackedConcat.proof
