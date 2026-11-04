import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.assocEmptyNum.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/assoc_empty_num/assoc_empty_num.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "empty-associative-num fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "empty-associative-num fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.assocEmptyNum.proof
