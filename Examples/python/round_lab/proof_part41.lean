import Examples.python.round_lab.proof_part40

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_thirty_one :
    round_lab.round_float_thirty_one(Float64.ofBits 0x00fad538f71e3153) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
