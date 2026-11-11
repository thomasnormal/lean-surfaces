import Examples.python.round_lab.proof_part15

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_six :
    round_lab.round_float_six(Float64.ofBits 0x3ff3c0ca2a5b1d5d) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca600b0293) := by
  exact ⟨256, rfl⟩
