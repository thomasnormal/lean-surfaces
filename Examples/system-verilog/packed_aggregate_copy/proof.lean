import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.packedAggregateCopy.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/packed_aggregate_copy/packed_aggregate_copy.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "packed-aggregate-copy fixture failed to load")
  unless SelfCheck.runSelfCheck design 16384 == .ok ["PASS"] do
    throw (IO.userError "packed-aggregate-copy fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.packedAggregateCopy.proof
