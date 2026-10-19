import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.unpackedInit.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/unpacked_init/unpacked_init.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unpacked-init fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "unpacked-init fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.unpackedInit.proof
