import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.arrayReverseProcedural.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/array_reverse_procedural/array_reverse_procedural.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "procedural array-reverse fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "procedural array-reverse fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.arrayReverseProcedural.proof
