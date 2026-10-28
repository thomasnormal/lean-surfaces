import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.typenameEventDeclaration.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/typename_event_declaration/typename_event_declaration.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "typename-event-declaration fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "typename-event-declaration fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.typenameEventDeclaration.proof
