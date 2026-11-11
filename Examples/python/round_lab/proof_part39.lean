import Examples.python.round_lab.proof_part38

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_twenty_nine :
    round_lab.round_float_twenty_nine(Float64.ofBits 0x347beee1956a049f) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
