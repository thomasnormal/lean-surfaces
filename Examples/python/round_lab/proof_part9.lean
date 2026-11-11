import Examples.python.round_lab.proof_part8

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_int_positive :
    round_lab.round_int_positive(7) ==> Val.int 7 := by
  exact ⟨256, rfl⟩
