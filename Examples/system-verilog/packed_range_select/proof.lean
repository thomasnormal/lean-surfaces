import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.packedRangeSelect.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/packed_range_select/packed_range_select.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "packed-range-select fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "packed-range-select fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.packedRangeSelect.proof
