import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.local2stateDeclarations.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/local_2state_declarations/local_2state_declarations.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "local two-state declaration fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "local two-state declaration fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.local2stateDeclarations.proof
