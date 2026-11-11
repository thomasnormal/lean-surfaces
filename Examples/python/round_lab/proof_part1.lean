import Examples.python.round_lab.base

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_half :
    round_lab.round_float(Float64.ofBits 0x3fe0000000000000) ==> Val.int 0 := by
  exact ⟨256, rfl⟩
