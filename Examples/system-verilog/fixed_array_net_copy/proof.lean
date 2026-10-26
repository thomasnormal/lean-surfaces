import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedArrayNetCopy.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/fixed_array_net_copy/fixed_array_net_copy.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fixed-array-net-copy fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "fixed-array-net-copy fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedArrayNetCopy.proof
