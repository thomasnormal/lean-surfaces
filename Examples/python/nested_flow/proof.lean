/-
Proof module for `Examples/python/nested_flow/spec.lean` (three-file example
layout; see Examples/python/tri/proof.lean for the pattern rationale). Every
theorem stated in spec.lean is proved here under the same name; the spec
side is `:= by proofs` (Surface.lean). Statements are duplicated between
the two files BY DESIGN; the spec-side reference typechecks the
duplication. This file loads its own copy of the program literal.

THE CONTROL-FLOW STRESS PROOF (`py_vcgen`, VCTactic.lean): `first_factor`
layers a while inside a while, a `break` inside an `if` in the inner body,
and a `return` out of the middle of the outer loop — three shapes
`py_begin`/`py_loop` cannot open at once. `py_vcgen` walks the whole
function from two `inv`/`dec` clause pairs plus one `exit2` fact:

* outer loop (`i`): `2 ≤ i` and nothing in `[2, i)` divides `n`; measure
  `n - i` (its decrease is the one nonlinear step, `2·i ≤ i·i ≤ n`);
* inner loop (`m`, created mid-body — it lives behind the invariant's
  symbolic environment tail, no hand-unrolled first iteration): `0 ≤ m`
  with `i ∣ n - m`; measure `m`;
* `exit2` (REQUIRED, break-carrying loop): `0 ≤ m < i ∧ i ∣ n - m` — the
  break site proves it from its branch fact `m < i`, the test-false exit
  from `m ≤ 0` plus the outer `2 ≤ i`.

Both `return` residuals land on one mathlib fact each: a first divisor is
`Nat.minFac` (`minFac_le_of_dvd` + minimality), and no divisor up to `√n`
makes `n` prime (`minFac_sq_le_self`). The `hn2` rebrand feeds `omega`,
which consumes only unbranded comparisons (AGENTS.md failure table).
-/
import LeanModels
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Ring

namespace Examples.python.nested_flow.proof

open LeanModels LeanModels.Python

load_program nested_flow from "Examples/python/nested_flow/nested_flow.json"

/-- A divisor `2 ≤ i` of `n` with nothing in `[2, i)` dividing `n` IS the
least prime factor. -/
private theorem eq_minFac_of_first_divisor {n i : Int} (hn : 2 ≤ n) (h2 : 2 ≤ i)
    (hmin : ∀ d : Int, 2 ≤ d → d < i → ¬d ∣ n) (hdvd : i ∣ n) :
    i = (n.toNat.minFac : Int) := by
  have hN : ((n.toNat : Int)) = n := Int.toNat_of_nonneg (by omega)
  have hle : n.toNat.minFac ≤ i.toNat := by
    refine Nat.minFac_le_of_dvd (by omega) ?_
    have h : ((i.toNat : Int)) ∣ ((n.toNat : Int)) := by
      rw [Int.toNat_of_nonneg (by omega : (0:Int) ≤ i), hN]; exact hdvd
    exact_mod_cast h
  have h2f : 2 ≤ n.toNat.minFac := (Nat.minFac_prime (by omega)).two_le
  have hdf : ((n.toNat.minFac : Int)) ∣ n := by
    have h := Int.natCast_dvd_natCast.mpr (Nat.minFac_dvd n.toNat)
    rwa [hN] at h
  by_contra hne
  exact hmin _ (by exact_mod_cast h2f) (by omega) hdf

/-- No divisor in `[2, i)` and `n < i·i` make `n` its own least prime
factor (`n` is prime — the trial-division bound). -/
private theorem eq_minFac_self_of_no_root_divisor {n i : Int} (hn : 2 ≤ n)
    (h2 : 2 ≤ i) (hii : n < i * i)
    (hmin : ∀ d : Int, 2 ≤ d → d < i → ¬d ∣ n) :
    n = (n.toNat.minFac : Int) := by
  have hN : ((n.toNat : Int)) = n := Int.toNat_of_nonneg (by omega)
  have hp : n.toNat.Prime := by
    by_contra hnp
    have hsq := Nat.minFac_sq_le_self (n := n.toNat) (by omega) hnp
    have h2f : 2 ≤ n.toNat.minFac := (Nat.minFac_prime (by omega)).two_le
    have hdf : ((n.toNat.minFac : Int)) ∣ n := by
      have h := Int.natCast_dvd_natCast.mpr (Nat.minFac_dvd n.toNat)
      rwa [hN] at h
    have hff : ((n.toNat.minFac : Int)) * ((n.toNat.minFac : Int)) ≤ n := by
      have h : ((n.toNat.minFac ^ 2 : Nat) : Int) ≤ ((n.toNat : Int)) :=
        Int.ofNat_le.mpr hsq
      rw [hN] at h
      calc ((n.toNat.minFac : Int)) * ((n.toNat.minFac : Int))
          = ((n.toNat.minFac ^ 2 : Nat) : Int) := by push_cast [pow_two]; ring
        _ ≤ n := h
    refine hmin _ (by exact_mod_cast h2f) ?_ hdf
    by_contra hge
    have hmul : i * i ≤ ((n.toNat.minFac : Int)) * ((n.toNat.minFac : Int)) :=
      Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
    exact absurd hii (Int.not_lt.mpr (Int.le_trans hmul hff))
  rw [hp.minFac_eq, hN]

set_option maxHeartbeats 1000000 in
/-- Total correctness through the layered control flow, by `py_vcgen` from
two clause pairs plus the `exit2` fact (module docstring). Residuals in
walk order: outer init (vacuous minimality), outer exit fact, inner init,
inner test-false exit, inner preservation (divisibility survives the
subtraction), inner decrease, the mid-loop `return i` (first divisor =
`minFac`), outer preservation (range, then minimality — `i ∤ n` because
the inner loop left `m' ≠ 0`), outer decrease (the nonlinear
`2·i ≤ i·i ≤ n` step), and the post-loop `return n` (no divisor up to
`√n`, so `n` is prime). -/
theorem first_factor_total (n : PyInt) (hn : 2 ≤ n) :
    nested_flow.first_factor(n) ==> (n.toNat.minFac : PyInt) := by
  have hn2 : (2 : Int) ≤ n := hn
  py_vcgen [nested_flow]
    (inv1 := fun (i : Int) => 2 ≤ i ∧ ∀ d : Int, 2 ≤ d → d < i → ¬ d ∣ n)
    (dec1 := fun (i : Int) => (n - i).toNat)
    (inv2 := fun (m : Int) => 0 ≤ m ∧ i ∣ (n - m))
    (dec2 := fun (m : Int) => m.toNat)
    (exit2 := fun (m : Int) => 0 ≤ m ∧ m < i ∧ i ∣ (n - m))
  · intro d h1 h2; omega
  · exact ⟨hcore, hx⟩
  · omega
  · exact ⟨m, ⟨tl, rfl⟩, hcore, hcore.1, by omega, hcore.2⟩
  · obtain ⟨k, hk⟩ := hinv2
    exact ⟨k + 1, by grind⟩
  · omega
  · exact eq_minFac_of_first_divisor hn ‹2 ≤ i›
      ‹∀ d : Int, 2 ≤ d → d < i → ¬ d ∣ n› (by simpa [hif] using hinv2)
  · omega
  · intro d hd2 hdi hdvd
    rcases (by omega : d < i ∨ d = i) with h | heq
    · exact ‹∀ d : Int, 2 ≤ d → d < i → ¬ d ∣ n› d hd2 h hdvd
    · have him : i ∣ m' := by
        have h := Int.dvd_sub (heq ▸ hdvd : i ∣ n) hinv2
        rwa [show n - (n - m') = m' by ring] at h
      exact hif (Int.eq_zero_of_dvd_of_nonneg_of_lt hinv1 hcont.2.1 him)
  · have h : 2 * i ≤ i * i := Int.mul_le_mul_of_nonneg_right ‹2 ≤ i› (by omega)
    have h2 : 2 * i ≤ n := Int.le_trans h ‹i * i ≤ n›
    omega
  · exact eq_minFac_self_of_no_root_divisor hn hinv1 hcont hinv2

/-- Typed relational corollary of `first_factor_total` (determinism modulo
fuel) — one `py_corollary` (Surface.lean). -/
theorem first_factor_correct (n r : PyInt) (hn : 2 ≤ n)
    (h : nested_flow.first_factor(n) ⇓ r) : r = (n.toNat.minFac : PyInt) := by
  py_corollary [first_factor_total]

end Examples.python.nested_flow.proof
