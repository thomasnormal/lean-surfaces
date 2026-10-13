import LeanModels.Sv.SelfCheck
import LeanModels.Sv.Obs

namespace Examples.systemVerilog.increment.proof

open LeanModels.Sv

set_option autoImplicit false

theorem four_state_increment_wrap :
    LVec.add (.ofNat 4 15) (.ofNat 4 1) = .ofNat 4 0 := by
  simp [LVec.add, LVec.toNat?_ofNat, LVec.arithWidth, LVec.width_ofNat]
  rw [← LVec.ofNat_emod]

#print axioms four_state_increment_wrap

end Examples.systemVerilog.increment.proof
