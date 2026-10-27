import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.sformatfZeroWidth.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/sformatf_zero_width/sformatf_zero_width.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "sformatf zero-width fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["1010|a|42|012"] do
    throw (IO.userError "sformatf zero-width fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.sformatfZeroWidth.proof
