import Examples.python.round_lab.proof_part35

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_twenty_six :
    round_lab.round_float_twenty_six(Float64.ofBits 0x8328aa3794629f05) ==>
      Val.float (Float64.ofBits 0x8000000000000000) := by
  exact ⟨256, rfl⟩
