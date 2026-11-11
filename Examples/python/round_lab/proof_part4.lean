import Examples.python.round_lab.proof_part3

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_nan :
    round_lab.round_float_nan() ==>!
      (.valueError "cannot convert float NaN to integer") := by
  exact ⟨256, rfl⟩
