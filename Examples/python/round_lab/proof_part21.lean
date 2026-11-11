import Examples.python.round_lab.proof_part20

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_eleven :
    round_lab.round_float_eleven(Float64.ofBits 0x3ff3c0ca43bce284) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bd3a7a) := by
  exact ⟨256, rfl⟩
