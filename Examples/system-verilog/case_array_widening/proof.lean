import LeanModels.Sv.Load

namespace Examples.systemVerilog.caseArrayWidening.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def fixtureReceipt : IO Unit := do
  let .ok design := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/case_array_widening/case_array_widening.sv.json")
    | throw (IO.userError "case-array-widening fixture failed to load")
  unless runSelfCheck design 32768 == .ok ["PASS"] do
    throw (IO.userError "case-array-widening fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.caseArrayWidening.proof
