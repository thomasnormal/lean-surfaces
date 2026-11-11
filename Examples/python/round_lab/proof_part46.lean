import Examples.python.round_lab.proof_part45

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_thirty_six :
    round_lab.round_float_thirty_six(Float64.ofBits 0x0000000000000001) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
