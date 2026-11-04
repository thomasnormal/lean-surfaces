import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedArraySort.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/fixed_array_sort/fixed_array_sort.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fixed-array sort fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["SORT PASS", "RSORT PASS"] do
    throw (IO.userError "fixed-array sort fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedArraySort.proof
