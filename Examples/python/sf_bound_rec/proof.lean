/-
Real proofs for Examples/python/sf_bound_rec/spec.lean.

`sfSearchMoves` is a verbatim copy (modulo the score callback, pre-applied
because the children's scores are precomputed) of `searchMoves` in
sunfish's hand-written formal tree, formal/Sunfish/Bound.lean:

    def searchMoves {α} (gamma : Int) (score : α → Int) :
        List α → Int → Int
      | [], best => best
      | m :: ms, best =>
        if gamma ≤ max best (score m) then max best (score m)
        else searchMoves gamma score ms (max best (score m))

Proving the tier-shaped Python recursion returns exactly
`sfSearchMoves gamma scores best` machine-checks the Python-to-Lean-model
transcription step that today is audited by hand.

Proof shape: the recursion is on an index into a fixed list, so the fib
strong-induction pattern is driven by a plain Nat bound on the remaining
length (`scores.length - i.toNat ≤ n`), with the ag_clamp01 up-front
`by_cases` for the two sequential `if`s and the bisect `arrVal_getElem`
helper (copied — example-local by convention, AGENTS.md failure table)
for the symbolic subscript.
-/
import LeanModels

namespace Examples.python.sf_bound_rec.proof

open LeanModels LeanModels.Python

load_program sf_bound_rec from "Examples/python/sf_bound_rec/sf_bound_rec.json"

/-- Root-namespace model constant (fib's rationale: the twin statements
must mention the SAME recursive constant). Verbatim
`formal/Sunfish/Bound.lean` `searchMoves`, score callback pre-applied. -/
def _root_.sfSearchMoves (gamma : Int) : List Int → Int → Int
  | [], best => best
  | s :: rest, best =>
    if gamma ≤ max best s then max best s
    else sfSearchMoves gamma rest (max best s)

-- `getD_eq_getElem` and `arrVal_getElem` (the `getElem?` normal form a
-- symbolic subscript read leaves behind) are the SHARED spec-side lemmas
-- (VCTactic.lean §marshalled-list indexing) — they were copied here, into
-- `bench_bisect` and into `bench_statistics` until the family was promoted.

/-- The guard exit: past the end of `scores` the run returns `best`. The
recursive branch is unreachable here, and pruning it is arithmetic the
walker's branch normalization does not do, so this one stays a direct
symbolic run. -/
private theorem bound_rec_exit (scores : List PyInt) (gamma i best : PyInt)
    (hge : (scores.length : Int) ≤ i) :
    sf_bound_rec.bound_rec(scores, gamma, i, best) ==> best := by
  refine ⟨64, ?_⟩
  unfold callFunction; rw [callIn.eq_2]
  py_simp [sf_bound_rec, show ((scores.length : Int) ≤ i) from hge]

set_option maxHeartbeats 1600000 in
/-- **Total correctness** of the general index-carrying form: from index
`i`, the run returns `sfSearchMoves gamma (scores.drop i.toNat) best`.

The recursion is on an index into a fixed list, so the induction is a
plain `Nat` bound on the remaining length. Inside it, one `py_vcgen` call
walks the whole body — the two sequential `if`s, the symbolic subscript,
and the recursive `return bound_rec(…)`, whose callee fact is the IH
itself (a ∀-quantified local hypothesis, instantiated at the branch's own
`b`). What is left is the mathematics: peel one element off the scanned
suffix and `sfSearchMoves` steps. -/
theorem bound_rec_total (scores : List PyInt) (gamma i best : PyInt)
    (hi : 0 ≤ i) :
    sf_bound_rec.bound_rec(scores, gamma, i, best) ==>
      sfSearchMoves gamma (scores.drop i.toNat) best := by
  -- `i`/`best` are ascribed at `Int`, not `PyInt`: `omega` does not see a
  -- hypothesis or a goal whose type is the abbreviation (measured — it is
  -- why this gallery writes `(i : Int)` everywhere), and every arithmetic
  -- side condition below goes through it
  have key : ∀ (n : Nat) (i best : Int), (0 : Int) ≤ i →
      (scores.length : Int) ≤ i + (n : Int) →
      sf_bound_rec.bound_rec(scores, gamma, i, best) ==>
        sfSearchMoves gamma (scores.drop i.toNat) best := by
    intro n
    induction n with
    | zero =>
      intro i best hi0 hle
      have hdrop : scores.drop i.toNat = [] :=
        List.drop_eq_nil_of_le (by omega)
      have h := bound_rec_exit scores gamma i best (by omega)
      simpa [hdrop, sfSearchMoves] using h
    | succ n ihn =>
      intro i best hi0 hle
      by_cases hlt : (i : Int) < scores.length
      · have ih : ∀ b : Int,
            sf_bound_rec.bound_rec(scores, gamma, i + 1, b) ==>
              sfSearchMoves gamma (scores.drop (i + 1).toNat) b :=
          fun b => ihn (i + 1) b (by omega) (by omega)
        have hcons : scores.drop i.toNat
            = scores[i.toNat] :: scores.drop (i + 1).toNat := by
          rw [show (i + 1).toNat = i.toNat + 1 from by omega]
          exact List.drop_eq_getElem_cons (by omega)
        py_vcgen [sf_bound_rec]
        all_goals grind [sfSearchMoves]
      · have hdrop : scores.drop i.toNat = [] :=
          List.drop_eq_nil_of_le (by omega)
        have h := bound_rec_exit scores gamma i best (by omega)
        simpa [hdrop, sfSearchMoves] using h
  have hi' : (0 : Int) ≤ i := hi
  exact key scores.length i best hi' (by omega)

/-- The headline form: from the top of the move loop
(`i = 0`, `best = -MATE_UPPER = -69290`), the Python recursion computes
exactly `formal/Sunfish/Bound.lean`'s `searchMoves gamma · scores LOSS`. -/
theorem bound_rec_search (scores : List PyInt) (gamma : PyInt) :
    sf_bound_rec.bound_rec(scores, gamma, 0, -69290) ==>
      sfSearchMoves gamma scores (-69290) := by
  have h := bound_rec_total scores gamma 0 (-69290) (Int.le_refl 0)
  simpa using h

end Examples.python.sf_bound_rec.proof
