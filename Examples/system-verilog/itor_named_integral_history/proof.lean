import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.itorNamedIntegralHistory.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/itor_named_integral_history/itor_named_integral_history.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "itor-named-integral-history fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "itor-named-integral-history fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.itorNamedIntegralHistory.proof
