/-
Real proofs for Examples/python/sf_bound_loop/spec.lean.

The model function `searchMoves` is a verbatim copy (modulo the score
callback, pre-applied here because the children's scores are precomputed)
of `searchMoves` in sunfish's hand-written formal tree
(formal/Sunfish/Bound.lean). Proving the tier-shaped Python loop returns
exactly `searchMoves gamma scores (-69290)` machine-checks the
Python-loop-to-Lean-model transcription step that used to be audited by
hand.

This file was `proof.lean.blocked-by-py_vcgen-gaps` from the day it was
written until 2026-08-16, and the two gaps it was named for are both shut:
a builtin call under the loop's symbolic environment tail (the invariant
carries `Env.lookup tl "<callee>" = none` now), and the SUBSCRIPT
`scores[i]`, whose range guard and negative-index fold are interpreter
`ite` CONDITIONS — not rewrite side conditions — and so needed arithmetic
inside the captured run's simp set, not a discharger beside it
(`decideArith`, VCTactic.lean). What is left below is only the
mathematics: peel one element off the scanned suffix, or none at all past
the end, and `searchMoves` steps.
-/
import LeanModels

namespace Examples.python.sf_bound_loop.proof

open LeanModels LeanModels.Python

load_program sf_bound_loop from "Examples/python/sf_bound_loop/sf_bound_loop.json"

/-- The fail-soft best loop with beta cutoff — `formal/Sunfish/Bound.lean`'s
`searchMoves gamma score`, with `score` pre-applied (scores precomputed). -/
def searchMoves (gamma : Int) : List Int → Int → Int
  | [], best => best
  | s :: rest, best =>
    if gamma ≤ max best s then max best s
    else searchMoves gamma rest (max best s)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem bound_loop_total (scores : List PyInt) (gamma : PyInt) :
    sf_bound_loop.bound_loop(scores, gamma) ==>
      searchMoves gamma scores (-69290) := by
  py_vcgen [sf_bound_loop]
    (inv := fun (best i : Int) =>
      0 ≤ i ∧ i ≤ scores.length ∧
      searchMoves gamma scores (-69290) =
        searchMoves gamma (scores.drop i.toNat) best)
    (dec := fun (best i : Int) => (scores.length - i).toNat)
    (exit := fun (best i : Int) =>
      searchMoves gamma scores (-69290) = best)
  -- the mathematics the walker leaves: peel one element off the scanned
  -- suffix (or, past the end, none at all) and `searchMoves` steps
  all_goals
    first
      | (have hnil : List.drop i.toNat scores = [] :=
           List.drop_eq_nil_of_le (by omega)
         grind [searchMoves])
      | (have hcons : List.drop i.toNat scores
             = scores[i.toNat] :: List.drop (i + 1).toNat scores := by
           rw [show (i + 1).toNat = i.toNat + 1 from by omega]
           exact List.drop_eq_getElem_cons (by omega)
         grind [searchMoves])
      | grind [searchMoves]

end Examples.python.sf_bound_loop.proof
