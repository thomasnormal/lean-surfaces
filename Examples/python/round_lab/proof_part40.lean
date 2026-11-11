import Examples.python.round_lab.proof_part39

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_thirty :
    round_lab.round_float_thirty(Float64.ofBits 0x034386046695a3a1) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
