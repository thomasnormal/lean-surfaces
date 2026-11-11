import Examples.python.round_lab.proof_part11

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_two :
    round_lab.round_float_two(Float64.ofBits 0x3ff3c083126e978d) ==>
      Val.float (Float64.ofBits 0x3ff3ae147ae147ae) := by
  exact ⟨256, rfl⟩
