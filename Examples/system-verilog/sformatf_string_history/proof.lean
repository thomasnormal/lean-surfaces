import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.sformatfStringHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/sformatf_string_history/sformatf_string_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "sformatf string-history fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["hello"] do
    throw (IO.userError "sformatf string-history fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.sformatfStringHistory.proof
