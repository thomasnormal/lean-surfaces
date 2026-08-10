/-
Real proofs for Examples/python/sf_bound_for/spec.lean.

THE STEP-2 MILESTONE: sunfish.py's fail-soft cutoff loop in near-verbatim
form — `best = -MATE_UPPER` (G1 module constant), `for score in scores:`
(step-2 `for`), `best = max(best, score)` (B1 builtin), the beta-cutoff
`break` — proved to compute exactly `sfSearchMoves`, the verbatim copy of
`searchMoves` from sunfish's hand-written formal tree
(formal/Sunfish/Bound.lean), IMPORTED from sf_bound_rec: the index-
recursion form and this `for` form are certified against the SAME model
constant.

Proof shape: `execFor` is a frozen recursion point (like `execWhile`) —
unfold exactly one step with `rw [execFor.eq_2/eq_3]`, never via the simp
set. `key` is a list induction over it in fuel-threshold form
(`execFor_mono` generalizes each concrete-fuel run), stated at the
uniform post-first-iteration environment shape (`score` bound). The main
theorem unrolls the first iteration by hand — the target variable is
CREATED by it, so the environment grows mid-loop (the F-2 shape) — and
splices `key` for the tail.
-/
import Examples.python.sf_bound_rec.proof

namespace Examples.python.sf_bound_for.proof

open LeanModels LeanModels.Python

load_program sf_bound_for from "Examples/python/sf_bound_for/sf_bound_for.json"

/-- The pinned world of the heap-free geometry (`initWorld` unfolded —
since the G1 world-init the module's constant global rides in it). -/
private def pw : World := ⟨#[], [("MATE_UPPER", .int 69290)], []⟩

/-- The loop target of `bound_loop`'s `for` (the loaded literal's piece). -/
private def loopTgt : Expr :=
  .name "score" { lineno := 20, colOffset := 8, endLineno := 20, endColOffset := 13 }

/-- The loop body of `bound_loop`'s `for` (the loaded literal's pieces):
`best = max(best, score)` and `if best >= gamma: break`. -/
private def loopBody : List Stmt :=
  [.assign
      #[.name "best" { lineno := 21, colOffset := 8, endLineno := 21, endColOffset := 12 }]
      (.call
        (.name "max" { lineno := 21, colOffset := 15, endLineno := 21, endColOffset := 18 })
        #[.name "best" { lineno := 21, colOffset := 19, endLineno := 21, endColOffset := 23 },
          .name "score" { lineno := 21, colOffset := 25, endLineno := 21, endColOffset := 30 }]
        #[]
        Option.none
        { lineno := 21, colOffset := 15, endLineno := 21, endColOffset := 31 })
      { lineno := 21, colOffset := 8, endLineno := 21, endColOffset := 31 },
   .ifStmt
      (.compare
        (.name "best" { lineno := 22, colOffset := 11, endLineno := 22, endColOffset := 15 })
        #[.gtE]
        #[.name "gamma" { lineno := 22, colOffset := 19, endLineno := 22, endColOffset := 24 }]
        { lineno := 22, colOffset := 11, endLineno := 22, endColOffset := 24 })
      #[.brk { lineno := 23, colOffset := 12, endLineno := 23, endColOffset := 17 }]
      #[]
      { lineno := 22, colOffset := 8, endLineno := 23, endColOffset := 17 }]

/-- The uniform loop environment: params, the running `best`, the loop
variable `score` (present from the first iteration on). -/
private def E (scores : List Int) (gamma b s : Int) : Env :=
  [("scores", RVal.listV ((scores.map (RVal.thaw ∘ ToVal.toVal)).toArray)),
   ("gamma", RVal.int gamma), ("best", RVal.int b), ("score", RVal.int s)]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- The loop lemma: from the uniform shape, running the `for` tail over
`xs` folds `sfSearchMoves` into `best`. Fuel-threshold form; `s'` is the
final `score` slot. -/
private theorem key (scores : List Int) (gamma : Int) :
    ∀ (xs : List Int) (b s : Int),
      ∃ f₀ s', ∀ F, f₀ ≤ F →
        execFor sf_bound_for F ⟨pw, E scores gamma b s⟩
            loopTgt (xs.map (RVal.thaw ∘ ToVal.toVal)) loopBody
          = .ok ⟨pw, E scores gamma (sfSearchMoves gamma xs b) s'⟩ .next := by
  intro xs
  induction xs with
  | nil =>
    intro b s
    refine ⟨1, s, fun F hF => ?_⟩
    have hrun : execFor sf_bound_for 1 ⟨pw, E scores gamma b s⟩
        loopTgt (([] : List Int).map (RVal.thaw ∘ ToVal.toVal)) loopBody
        = .ok ⟨pw, E scores gamma b s⟩ .next := by
      rw [List.map_nil, execFor.eq_2]
    have := execFor_mono hrun (by simp) F hF
    simpa [sfSearchMoves] using this
  | cons x rest ih =>
    intro b s
    by_cases hc : gamma ≤ max b x
    · -- cutoff: the first tail iteration breaks
      refine ⟨32, x, fun F hF => ?_⟩
      have hrun : execFor sf_bound_for 32 ⟨pw, E scores gamma b s⟩
          loopTgt ((x :: rest).map (RVal.thaw ∘ ToVal.toVal)) loopBody
          = .ok ⟨pw, E scores gamma (max b x) x⟩ .next := by
        rw [List.map_cons, execFor.eq_3]
        py_simp [pw, sf_bound_for, loopTgt, loopBody, E, toVal_int, hc]
      have := execFor_mono hrun (by simp) F hF
      simpa [sfSearchMoves, if_pos hc] using this
    · obtain ⟨f₁, s₁, h₁⟩ := ih (max b x) x
      refine ⟨f₁ + 32, s₁, fun F hF => ?_⟩
      have hrun : execFor sf_bound_for (f₁ + 32) ⟨pw, E scores gamma b s⟩
          loopTgt ((x :: rest).map (RVal.thaw ∘ ToVal.toVal)) loopBody
          = .ok ⟨pw, E scores gamma (sfSearchMoves gamma rest (max b x)) s₁⟩
                 .next := by
        rw [List.map_cons, execFor.eq_3]
        simp only [pw, sf_bound_for, E, loopTgt, loopBody] at h₁ ⊢
        py_simp [pw, sf_bound_for, toVal_int,
                 (show ¬ gamma ≤ max b x from hc)]
        simp (disch := omega) only [h₁]
      have := execFor_mono hrun (by simp) F hF
      simpa [sfSearchMoves, if_neg hc] using this

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- **Total correctness**: the near-verbatim sunfish cutoff loop computes
`formal/Sunfish/Bound.lean`'s `searchMoves gamma · scores LOSS`. -/
theorem bound_loop_total (scores : List PyInt) (gamma : PyInt) :
    sf_bound_for.bound_loop(scores, gamma) ==>
      sfSearchMoves gamma scores (-69290) := by
  cases scores with
  | nil =>
    refine ⟨64, ?_⟩
    unfold callFunction; rw [callIn.eq_2]
    py_simp [sf_bound_for]
    rw [execFor.eq_2]
    py_simp [sfSearchMoves]
  | cons s0 rest =>
    by_cases hc : gamma ≤ max (-69290 : Int) s0
    · -- the very first iteration breaks
      refine ⟨64, ?_⟩
      unfold callFunction; rw [callIn.eq_2]
      py_simp [sf_bound_for, toVal_int]
      rw [execFor.eq_3]
      py_simp [toVal_int, hc]
      py_simp [sfSearchMoves, if_pos hc]
    · -- unroll the first iteration by hand (env grows), splice `key`
      obtain ⟨f₁, s₁, h₁⟩ := key (s0 :: rest) gamma rest (max (-69290) s0) s0
      py_simp [pw, sf_bound_for, E, loopTgt, loopBody, toVal_int] at h₁
      refine ⟨f₁ + 64, ?_⟩
      unfold callFunction; rw [callIn.eq_2]
      py_simp [sf_bound_for, toVal_int]
      rw [execFor.eq_3]
      py_simp [toVal_int, (show ¬ gamma ≤ max (-69290 : Int) s0 from hc)]
      simp (disch := omega) only [h₁]
      py_simp [sfSearchMoves, if_neg hc]

end Examples.python.sf_bound_for.proof
