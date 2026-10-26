import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.typenameDiscarded.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/typename_discarded/typename_discarded.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "typename-discarded fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "typename-discarded fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.typenameDiscarded.proof
