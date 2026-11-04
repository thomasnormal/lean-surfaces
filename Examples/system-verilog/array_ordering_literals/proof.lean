import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.arrayOrderingLiterals.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/array_ordering_literals/array_ordering_literals.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "array-ordering fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "array-ordering fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.arrayOrderingLiterals.proof
