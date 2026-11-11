import Examples.python.round_lab.proof_part21

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_twelve :
    round_lab.round_float_twelve(Float64.ofBits 0x3ff3c0ca43bceb50) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bcf41b) := by
  exact ⟨256, rfl⟩
