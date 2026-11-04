import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedStringArrayLoops.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/fixed_string_array_loops/fixed_string_array_loops.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fixed-string-array loop fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "fixed-string-array loop self-check disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedStringArrayLoops.proof
