import Examples.python.round_lab.proof_part31

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_twenty_two :
    round_lab.round_float_twenty_two(Float64.ofBits 0xbcba01a69be3d55f) ==>
      Val.float (Float64.ofBits 0xbcba01a6bb68a42c) := by
  exact ⟨256, rfl⟩
