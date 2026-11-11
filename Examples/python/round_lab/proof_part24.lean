import Examples.python.round_lab.proof_part23

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_fourteen :
    round_lab.round_float_fourteen(Float64.ofBits 0x3ff3c0ca43bcec47) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bcec31) := by
  exact ⟨256, rfl⟩
