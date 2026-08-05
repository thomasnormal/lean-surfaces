/-
Examples/python/sf_arith — three-file example layout. Tier-shaped
transliterations of three one-line facts from sunfish.py (the sunfish
chess engine): the move/rotate score identity, the futility-pruning test
together with the equivalence its comment claims, and the deterministic
LMR amount. The point of `futility_comment_true`: the code and its comment
are proved to agree — a comment-vs-code divergence of exactly the kind a
manual model-fidelity audit hunts for is machine-checked absent here.
-/
import Examples.python.sf_arith.proof

open LeanModels LeanModels.Python

load_program sf_arith from "Examples/python/sf_arith/sf_arith.json"

/-! Non-vacuity: concrete runs (values cross-checked against CPython). -/
#py_check sf_arith.child_score(10, -25) = 15
#py_check sf_arith.child_score(0, 0) = 0
#py_check sf_arith.futility_margin(10, 5, 20) = 1
#py_check sf_arith.futility_margin(10, 5, 15) = 0
#py_check sf_arith.futility_margin(-100, 30, -69) = 1
#py_check sf_arith.lmr_amount(4, 8, -1) = 1
#py_check sf_arith.lmr_amount(3, 8, -1) = 0
#py_check sf_arith.lmr_amount(4, 7, -1) = 0
#py_check sf_arith.lmr_amount(4, 8, 0) = 0

/-- The score identity of `Position.move`+`rotate`:
`child.score = -(pos.score + pos.value(move))` — the `ValGame` structural
property behind `futilityOK_discharged` in sunfish's formal/ tree. -/
theorem child_score_spec (s v : PyInt) :
    sf_arith.child_score(s, v) ==> -(s + v) := by proofs

/-- The futility test as written: prunes iff `pos.score + val < gamma`. -/
theorem futility_code (s v g : PyInt) :
    sf_arith.futility_margin(s, v, g) ==>
      (if s + v < g then (1 : Int) else 0) := by proofs

/-- The futility test as its comment claims:
`"pos.score + val < gamma === -(pos.score + val) >= 1-gamma"`. Proving the
program against the COMMENT's form certifies comment↔code agreement. -/
theorem futility_comment_true (s v g : PyInt) :
    sf_arith.futility_margin(s, v, g) ==>
      (if 1 - g ≤ -(s + v) then (1 : Int) else 0) := by proofs

/-- Deterministic LMR: `LMR = int(depth >= 4 and i_m >= 8 and val < 0)`. -/
theorem lmr_spec (d i v : PyInt) :
    sf_arith.lmr_amount(d, i, v) ==>
      (if 4 ≤ d ∧ 8 ≤ i ∧ v < 0 then (1 : Int) else 0) := by proofs
