import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fseekStdoutError.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/fseek_stdout_error/fseek_stdout_error.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fseek-stdout-error fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "fseek-stdout-error fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fseekStdoutError.proof
