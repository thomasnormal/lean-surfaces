import LeanModels.Sv.Param
import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.clog2.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/clog2/clog2.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "clog2 fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "clog2 self-check disagrees")

#eval fixtureReceipt

theorem clog2_boundary_values :
    [clog2 0, clog2 1, clog2 8, clog2 9, clog2 32] = [0, 0, 3, 4, 5] := by
  decide

theorem clog2_negative_is_unsigned :
    clog2 (2 ^ 32 - 1) = 32 := by
  decide

#print axioms clog2_boundary_values
#print axioms clog2_negative_is_unsigned

end Examples.systemVerilog.clog2.proof
