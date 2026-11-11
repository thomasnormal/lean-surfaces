import Examples.python.round_lab.proof_part34

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_twenty_five :
    round_lab.round_float_twenty_five(Float64.ofBits 0x000044fa709cccc2) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
