import Examples.python.round_lab.proof_part27

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_eighteen :
    round_lab.round_float_eighteen(Float64.ofBits 0x3f296619b1800000) ==>
      Val.float (Float64.ofBits 0x3f296619b17ffff2) := by
  exact ⟨256, rfl⟩
