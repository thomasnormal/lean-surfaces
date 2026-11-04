import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.ftellStdoutError.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/ftell_stdout_error/ftell_stdout_error.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "ftell-stdout-error fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "ftell-stdout-error fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.ftellStdoutError.proof
