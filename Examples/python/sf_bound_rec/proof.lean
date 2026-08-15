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

/-- The guard exit: past the end of `scores` the run returns `best`. -/
private theorem bound_rec_exit (scores : List PyInt) (gamma i best : PyInt)
    (hge : (scores.length : Int) ≤ i) :
    sf_bound_rec.bound_rec(scores, gamma, i, best) ==> best := by
  refine ⟨64, ?_⟩
  unfold callFunction; rw [callIn.eq_2]
  py_simp [sf_bound_rec, show ((scores.length : Int) ≤ i) from hge]

set_option maxHeartbeats 1000000 in
/-- **Total correctness** of the general index-carrying form: from index
`i`, the run returns `sfSearchMoves gamma (scores.drop i.toNat) best`. -/
theorem bound_rec_total (scores : List PyInt) (gamma i best : PyInt)
    (hi : 0 ≤ i) :
    sf_bound_rec.bound_rec(scores, gamma, i, best) ==>
      sfSearchMoves gamma (scores.drop i.toNat) best := by
  have key : ∀ (n : Nat) (i best : Int), 0 ≤ i →
      scores.length - i.toNat ≤ n →
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
      · have hnn : ¬ ((i : Int) < 0) := by omega
        have hidxN : i.toNat < scores.length := by omega
        have hdrop := List.drop_eq_getElem_cons hidxN
        have harr := arrVal_getElem scores i.toNat hidxN
        have ht1 : ((i : Int) + 1).toNat = i.toNat + 1 := by omega
        have hle' : scores.length - ((i : Int) + 1).toNat ≤ n := by omega
        rw [hdrop]
        -- four branch combinations; the two cutoff ones are straight-line,
        -- the two continue ones splice the IH at (i + 1).
        by_cases hs : best < scores[i.toNat]
        · have hmax : max best (scores[i.toNat]) = scores[i.toNat] :=
            Int.max_eq_right (Int.le_of_lt hs)
          by_cases hb : gamma ≤ scores[i.toNat]
          · refine ⟨64, ?_⟩
            unfold callFunction; rw [callIn.eq_2]
            simp only [sfSearchMoves, hmax, if_pos hb]
            py_simp [sf_bound_rec, hnn, harr,
                     show ((0:Int) ≤ i ∧ i < (scores.length : Int)) by omega,
                     show ¬ ((scores.length : Int) ≤ i) by omega,
                     show best < scores[i.toNat] from hs,
                     show gamma ≤ scores[i.toNat] from hb]
          · py_lift ⟨f₁, h₁⟩ :=
              ihn ((i : Int) + 1) (scores[i.toNat]) (by omega) hle'
              with [sf_bound_rec]
            rw [ht1] at h₁
            refine ⟨f₁ + 64, ?_⟩
            unfold callFunction; rw [callIn.eq_2]
            simp only [sfSearchMoves, hmax, if_neg hb]
            py_simp [sf_bound_rec, hnn, harr,
                     show ((0:Int) ≤ i ∧ i < (scores.length : Int)) by omega,
                     show ¬ ((scores.length : Int) ≤ i) by omega,
                     show best < scores[i.toNat] from hs,
                     show ¬ (gamma ≤ scores[i.toNat]) from hb]
            simp (disch := omega) only [h₁]
            py_simp []
        · have hmax : max best (scores[i.toNat]) = best :=
            Int.max_eq_left (Int.not_lt.mp hs)
          by_cases hb : gamma ≤ best
          · refine ⟨64, ?_⟩
            unfold callFunction; rw [callIn.eq_2]
            simp only [sfSearchMoves, hmax, if_pos hb]
            py_simp [sf_bound_rec, hnn, harr,
                     show ((0:Int) ≤ i ∧ i < (scores.length : Int)) by omega,
                     show ¬ ((scores.length : Int) ≤ i) by omega,
                     show ¬ (best < scores[i.toNat]) from hs,
                     show gamma ≤ best from hb]
          · py_lift ⟨f₁, h₁⟩ :=
              ihn ((i : Int) + 1) best (by omega) hle'
              with [sf_bound_rec]
            rw [ht1] at h₁
            refine ⟨f₁ + 64, ?_⟩
            unfold callFunction; rw [callIn.eq_2]
            simp only [sfSearchMoves, hmax, if_neg hb]
            py_simp [sf_bound_rec, hnn, harr,
                     show ((0:Int) ≤ i ∧ i < (scores.length : Int)) by omega,
                     show ¬ ((scores.length : Int) ≤ i) by omega,
                     show ¬ (best < scores[i.toNat]) from hs,
                     show ¬ (gamma ≤ best) from hb]
            simp (disch := omega) only [h₁]
            py_simp []
      · have hdrop : scores.drop i.toNat = [] :=
          List.drop_eq_nil_of_le (by omega)
        have h := bound_rec_exit scores gamma i best (by omega)
        simpa [hdrop, sfSearchMoves] using h
  exact key (scores.length - i.toNat) i best hi (Nat.le_refl _)

/-- The headline form: from the top of the move loop
(`i = 0`, `best = -MATE_UPPER = -69290`), the Python recursion computes
exactly `formal/Sunfish/Bound.lean`'s `searchMoves gamma · scores LOSS`. -/
theorem bound_rec_search (scores : List PyInt) (gamma : PyInt) :
    sf_bound_rec.bound_rec(scores, gamma, 0, -69290) ==>
      sfSearchMoves gamma scores (-69290) := by
  have h := bound_rec_total scores gamma 0 (-69290) (Int.le_refl 0)
  simpa using h

end Examples.python.sf_bound_rec.proof
