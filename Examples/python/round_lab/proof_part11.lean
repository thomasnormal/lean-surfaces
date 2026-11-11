import Examples.python.round_lab.proof_part10

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_one :
    round_lab.round_float_one(Float64.ofBits 0x4005666666666666) ==>
      Val.float (Float64.ofBits 0x400599999999999a) := by
  exact ⟨256, rfl⟩
