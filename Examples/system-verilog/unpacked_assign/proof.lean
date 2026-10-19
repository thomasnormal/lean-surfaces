import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.unpackedAssign.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/unpacked_assign/unpacked_assign.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "unpacked-assign fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "unpacked-assign fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.unpackedAssign.proof
