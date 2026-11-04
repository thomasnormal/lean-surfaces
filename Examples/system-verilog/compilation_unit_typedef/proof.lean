import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.compilationUnitTypedef.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/compilation_unit_typedef/compilation_unit_typedef.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "compilation-unit typedef fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["a5", "PASS"] do
    throw (IO.userError "compilation-unit typedef fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.compilationUnitTypedef.proof
