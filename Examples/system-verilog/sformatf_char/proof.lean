import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.sformatfChar.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/sformatf_char/sformatf_char.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "sformatf character fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["A"] do
    throw (IO.userError "sformatf character fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.sformatfChar.proof
