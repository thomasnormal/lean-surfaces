import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.compilationUnitParameter.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/compilation_unit_parameter/compilation_unit_parameter.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "compilation-unit-parameter fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["8", "a5", "PASS"] do
    throw (IO.userError "compilation-unit-parameter self-check disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.compilationUnitParameter.proof
