import Examples.python.round_lab.proof_part13

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_four :
    round_lab.round_float_four(Float64.ofBits 0x3ff3c0c1fc8f3238) ==>
      Val.float (Float64.ofBits 0x3ff3c0ebedfa43fe) := by
  exact ⟨256, rfl⟩
