/-
Proof module for `Examples/python/bench_calendar/spec.lean` (three-file
example layout). Every theorem stated in spec.lean is proved here under
the same name; the spec side is `:= by proofs`, which resolves
`Examples.python.bench_calendar.proof.<decl>` (Surface.lean).

PROVENANCE OF THE PROOFS (benchmark cold-prover run, 2026-07-30): produced
by a cold prover agent working from the repo docs alone (docs/benchmark.md
"Cold-prover runs"), adapted to the house layout with the statements
unchanged. The agent's task pointed at the tier-blocked Luhn suites; it
verified the blockage read-only and fell back to the Band-B provable-now
rows exactly as docs/benchmark.md classified them.
-/
import LeanModels

namespace Examples.python.bench_calendar.proof

open LeanModels LeanModels.Python

load_program bench_calendar from "Examples/python/bench_calendar/bench_calendar.json"

/-- Number of leap years among `A+1, A+2, …, A+n` (`n` terms) — i.e. the
leap-year count over the half-open interval `(A, A+n]`, with the SAME
Gregorian predicate `isleap_spec` proves `isleap` decides (Python `%` is
`Int.fmod`). The reference count `leapdays_count` is measured against. -/
def leapCount (A : Int) : Nat → Int
  | 0 => 0
  | n + 1 =>
    leapCount A n +
      (if Int.fmod (A + (n : Int) + 1) 4 = 0 ∧
          (Int.fmod (A + (n : Int) + 1) 100 ≠ 0 ∨ Int.fmod (A + (n : Int) + 1) 400 = 0)
        then 1 else 0)

/-- `isleap` decides the Gregorian leap-year rule exactly. -/
theorem isleap_spec (y : PyInt) :
    bench_calendar.isleap(y) ==> decide (Int.fmod y 4 = 0 ∧ (Int.fmod y 100 ≠ 0 ∨ Int.fmod y 400 = 0)) := by
  by_cases h4 : Int.fmod y 4 = 0 <;>
  by_cases h100 : Int.fmod y 100 = 0 <;>
  by_cases h400 : Int.fmod y 400 = 0 <;>
  refine ⟨32, ?_⟩ <;>
  py_simp [callFunction, bench_calendar, h4, h100, h400] <;>
  grind

/-- `leapdays` computes exactly the CPython closed-form inclusion-exclusion
count (straight-line body: two `AugAssign`s then the arithmetic `return`). -/
theorem leapdays_arith (y1 y2 : PyInt) :
    bench_calendar.leapdays(y1, y2) ==>
      (((y2 - 1).fdiv 4 - (y1 - 1).fdiv 4)
        - ((y2 - 1).fdiv 100 - (y1 - 1).fdiv 100)
        + ((y2 - 1).fdiv 400 - (y1 - 1).fdiv 400)) := by
  py_prove [bench_calendar]

/-- Core counting identity, in `omega`-native `Int` `/`/`%` (`Int.ediv`/`emod`,
which agree with the Python `Int.fdiv`/`Int.fmod` for every positive
modulus — `Int.fdiv_eq_ediv_of_nonneg`/`Int.fmod_eq_emod_of_nonneg`, no sign
hypothesis on the dividend needed): the inclusion-exclusion closed form over
`(A, A+n]` equals the direct leap-year count over the same range, for every
`A` and every `n`. Proved by induction on `n`; the successor step is one
`omega` call discharging the "does the floor-divide quotient jump by
exactly 1 at a multiple" fact for moduli 4, 100, 400 simultaneously (`omega`
does not know `Int.fdiv`/`Int.fmod` themselves, hence this lemma is stated
over `/`/`%`, bridged to the `Int.fmod`-based `leapCount` predicate by the
`fmod_eq_emod` rewrites below). -/
theorem leapdays_count_formula (A : Int) : ∀ n : Nat,
    (((A + (n : Int)) / 4 - A / 4) - ((A + (n : Int)) / 100 - A / 100)
        + ((A + (n : Int)) / 400 - A / 400))
      = leapCount A n := by
  intro n
  induction n with
  | zero => simp [leapCount]
  | succ n ih =>
    simp only [leapCount, ← ih]
    have e4 : Int.fmod (A + (n : Int) + 1) 4 = (A + (n : Int) + 1) % 4 :=
      Int.fmod_eq_emod_of_nonneg _ (by omega)
    have e100 : Int.fmod (A + (n : Int) + 1) 100 = (A + (n : Int) + 1) % 100 :=
      Int.fmod_eq_emod_of_nonneg _ (by omega)
    have e400 : Int.fmod (A + (n : Int) + 1) 400 = (A + (n : Int) + 1) % 400 :=
      Int.fmod_eq_emod_of_nonneg _ (by omega)
    rw [e4, e100, e400]
    omega

/-- **The meaningful theorem.** For `y1 ≤ y2`, CPython's `leapdays(y1, y2)`
terminates and returns exactly the number of Gregorian leap years in the
half-open interval `[y1, y2)` — the `leapCount` reference count over
`(y1 - 1, y1 - 1 + (y2 - y1)] = (y1 - 1, y2 - 1] = [y1, y2)`, using the same
leap-year predicate `isleap_spec` proves the sibling function `isleap`
decides. Proof: rerun `leapdays_arith`, bridge every `Int.fdiv` (Python `//`)
occurrence to `Int.ediv` (Lean's `/`, valid unconditionally for the positive
literal moduli 4/100/400 — `Int.fdiv_eq_ediv_of_nonneg`), then apply
`leapdays_count_formula` at `A := y1 - 1`, `n := (y2 - y1).toNat` and align
the endpoint `(y1 - 1) + (y2 - y1) = y2 - 1` with `omega`. -/
theorem leapdays_count (y1 y2 : PyInt) (h : y1 ≤ y2) :
    bench_calendar.leapdays(y1, y2) ==> leapCount (y1 - 1) (y2 - y1).toNat := by
  have harith := leapdays_arith y1 y2
  have hval :
      (((y2 - 1).fdiv 4 - (y1 - 1).fdiv 4) - ((y2 - 1).fdiv 100 - (y1 - 1).fdiv 100)
          + ((y2 - 1).fdiv 400 - (y1 - 1).fdiv 400))
        = leapCount (y1 - 1) (y2 - y1).toNat := by
    have b4 : (y2 - 1).fdiv 4 = (y2 - 1) / 4 := Int.fdiv_eq_ediv_of_nonneg _ (by omega)
    have b4' : (y1 - 1).fdiv 4 = (y1 - 1) / 4 := Int.fdiv_eq_ediv_of_nonneg _ (by omega)
    have b100 : (y2 - 1).fdiv 100 = (y2 - 1) / 100 := Int.fdiv_eq_ediv_of_nonneg _ (by omega)
    have b100' : (y1 - 1).fdiv 100 = (y1 - 1) / 100 := Int.fdiv_eq_ediv_of_nonneg _ (by omega)
    have b400 : (y2 - 1).fdiv 400 = (y2 - 1) / 400 := Int.fdiv_eq_ediv_of_nonneg _ (by omega)
    have b400' : (y1 - 1).fdiv 400 = (y1 - 1) / 400 := Int.fdiv_eq_ediv_of_nonneg _ (by omega)
    rw [b4, b4', b100, b100', b400, b400']
    have hcast : ((y2 - y1).toNat : Int) = y2 - y1 :=
      Int.toNat_of_nonneg (Int.sub_nonneg_of_le h)
    have hform := leapdays_count_formula (y1 - 1) (y2 - y1).toNat
    rw [hcast] at hform
    have e : (y1 - 1) + (y2 - y1) = y2 - 1 := by grind
    rw [e] at hform
    exact hform
  rw [hval] at harith
  exact harith

end Examples.python.bench_calendar.proof
