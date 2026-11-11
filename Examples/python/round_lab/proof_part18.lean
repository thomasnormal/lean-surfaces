import Examples.python.round_lab.proof_part17

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_eight :
    round_lab.round_float_eight(Float64.ofBits 0x3ff3c0ca43db770a) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca45330ff8) := by
  exact ⟨256, rfl⟩
