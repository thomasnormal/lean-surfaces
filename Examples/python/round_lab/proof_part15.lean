import Examples.python.round_lab.proof_part14

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_five :
    round_lab.round_float_five(Float64.ofBits 0x3ff3c0c9539b8887) ==>
      Val.float (Float64.ofBits 0x3ff3c0cc78e9f6a9) := by
  exact ⟨256, rfl⟩
