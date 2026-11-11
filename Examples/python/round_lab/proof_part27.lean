import Examples.python.round_lab.proof_part26

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_seventeen :
    round_lab.round_float_seventeen(Float64.ofBits 0x3f4b6113d6000000) ==>
      Val.float (Float64.ofBits 0x3f4b6113d600001c) := by
  exact ⟨256, rfl⟩
