import Examples.python.round_lab.proof_part19

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_ten :
    round_lab.round_float_ten(Float64.ofBits 0x3ff3c0ca43bc8a8e) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bffa2a) := by
  exact ⟨256, rfl⟩
