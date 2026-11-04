import LeanModels.Sv.Load

namespace Examples.systemVerilog.twoStateOutput.proof

open LeanModels.Sv
open LeanModels.Sv.SelfCheck

set_option autoImplicit false

def twoStateOutputReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/two_state_output/two_state_output.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "two-state output fixture failed to load")
  let some port := design.decls[0]?
    | throw (IO.userError "two-state output declaration missing")
  unless port.isOutput && port.twoState && port.width == 1 do
    throw (IO.userError "two-state output metadata was not retained")
  unless runSelfCheck design 4096 == Res.ok ["PASS"] do
    throw (IO.userError "two-state output did not initialize to zero")

#eval twoStateOutputReceipt

end Examples.systemVerilog.twoStateOutput.proof
