import Examples.python.round_lab.proof_part22

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_thirteen :
    round_lab.round_float_thirteen(Float64.ofBits 0x3ff3c0ca43bcec31) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bced12) := by
  exact ⟨256, rfl⟩
