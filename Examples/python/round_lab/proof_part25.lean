import Examples.python.round_lab.proof_part24

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_fifteen :
    round_lab.round_float_fifteen(Float64.ofBits 0x3ff3c0ca43bcec4a) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bcec4c) := by
  exact ⟨256, rfl⟩
