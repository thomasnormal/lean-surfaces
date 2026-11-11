import Examples.python.round_lab.proof_part12

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_three :
    round_lab.round_float_three(Float64.ofBits 0x3ff3c083126e978d) ==>
      Val.float (Float64.ofBits 0x3ff3be76c8b43958) := by
  exact ⟨256, rfl⟩
