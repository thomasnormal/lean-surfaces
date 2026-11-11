import Examples.python.round_lab.proof_part4

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_infinity :
    round_lab.round_float_infinity() ==>!
      (.overflowError "cannot convert float infinity to integer") := by
  exact ⟨256, rfl⟩
