import Examples.python.round_lab.proof_part29

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_twenty :
    round_lab.round_float_twenty(Float64.ofBits 0xbe6abc642d583e42) ==>
      Val.float (Float64.ofBits 0xbe6abc642d583fca) := by
  exact ⟨256, rfl⟩
