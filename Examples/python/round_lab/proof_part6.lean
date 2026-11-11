import Examples.python.round_lab.proof_part5

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_zero :
    round_lab.round_float_zero(Float64.ofBits 0x3ff8000000000000) ==>
      Val.float (Float64.ofBits 0x4000000000000000) := by
  exact ⟨256, rfl⟩
