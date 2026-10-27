import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedArraySelfCopy.proof

open LeanModels.Sv
open LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/fixed_array_self_copy/fixed_array_self_copy.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "fixed-array self-copy fixture failed to load")
  unless runSelfCheck design 4096 == .ok ["selfcopy 3 7"] do
    throw (IO.userError "fixed-array self-copy fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedArraySelfCopy.proof
