import Examples.python.round_lab.proof_part41

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_thirty_two :
    round_lab.round_float_thirty_two(Float64.ofBits 0x00000002e193c03a) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
