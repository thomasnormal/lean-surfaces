import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.insideParameterAdapter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/inside_parameter_adapter/inside_parameter_adapter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "inside parameter adapter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["0", "PASS"] do
    throw (IO.userError "inside parameter adapter fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.insideParameterAdapter.proof
