import Examples.python.round_lab.proof_part7

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_bool_zero :
    round_lab.round_bool_zero(true) ==> Val.int 1 := by
  exact ⟨256, rfl⟩
