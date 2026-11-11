import Examples.python.round_lab.proof_part25

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_sixteen :
    round_lab.round_float_sixteen(Float64.ofBits 0xbfcc61aba94c9000) ==>
      Val.float (Float64.ofBits 0xbfcc61aba94c8fff) := by
  exact ⟨256, rfl⟩
