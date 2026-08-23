/-
# SoftFloat, layer 2 — CORRECT ROUNDING, DECLARATIVELY

THE SPEC HALF, and it is the half that carries the weight.

charter §3.5.2 warns that a downstream proof must target ROUND-OF-EXACT and
never our bit algorithm: *"these output bits equal what `UnpackedFloat.div`
computes" is a tautology about an implementation.*  A COMPUTABLE `roundQ`
cannot escape that on its own — any correct implementation will structurally
resemble core's, so an `op_correct` stated against it would be close to
circular.

The escape is the family's spec/interpreter split one level down (charter
§3.3): the predicates below mention NO ALGORITHM at all — not core's, not
ours — and say only what IEEE 754-2019 §4.3 says: *the representable value
nearest the exact one, ties as the mode directs*.  `op_correct` is stated
against THIS; a computable `roundQ` is then proved to satisfy it, and its
resemblance to core stops mattering.

Nothing here mentions `Float`, `Float32`, or any core operation, and ℝ never
appears.  Width-parametric throughout: every definition takes `fmt : Format`.
-/
import LeanModels.SoftFloat.Basic

namespace LeanModels.SoftFloat

open Float.Model

/-! ## 1. REPRESENTABILITY — IEEE 754-2019 §3.3, arithmetically

The finite values a format holds are `± m · 2 ^ e` with the significand inside
`2 ^ mantissaBits` and the exponent at or above `minExponent`.

NOTE, stated rather than omitted: this carries NO UPPER bound on `e`, so it
describes the format's finite values as if the exponent range were unbounded
above.  Overflow is IEEE §7.4 and is a SEPARATE clause with its own
mode-dependent answer (charter §3.5); folding it in here would silently make
"nearest representable" mean "nearest representable or ±∞", which is a
different theorem.
-/
def ReprQ (fmt : Format) (q : Q) : Prop :=
  ∃ (m : Int) (e : Int),
    m.natAbs < 2 ^ fmt.mantissaBits ∧ fmt.minExponent ≤ e ∧ Q.Eq q (Q.dyadic m e)

/-! ## 2. CORRECT ROUNDING — IEEE 754-2019 §4.3, declaratively

No algorithm appears: `y` is representable, nothing representable is strictly
closer to `q`, and the tie rule picks between the two that can be equidistant.
-/

/-- §4.3.1 roundTiesToEven, and the tie clause is a PARAMETER of the shape, not
    baked in — `tieOk` is what distinguishes the two nearest modes. -/
structure IsNearest (fmt : Format) (q y : Q) (tieOk : Q → Prop) : Prop where
  /-- the answer is a value the format holds -/
  repr : ReprQ fmt y
  /-- nothing the format holds is strictly closer -/
  nearest : ∀ z, ReprQ fmt z → Q.Le (Q.dist q y) (Q.dist q z)
  /-- when some other representable value is EXACTLY as close, the tie rule decides -/
  tie : (∃ z, ReprQ fmt z ∧ ¬ Q.Eq z y ∧ Q.Eq (Q.dist q z) (Q.dist q y)) → tieOk y

/-- §4.3.2 the directed modes: `y` is representable, on the required side of `q`,
    and nothing representable lies strictly between `y` and `q`. -/
structure IsDirected (fmt : Format) (q y : Q) (side : Q → Q → Prop) : Prop where
  /-- the answer is a value the format holds -/
  repr : ReprQ fmt y
  /-- it lies on the side of `q` the mode requires -/
  onSide : side y q
  /-- nothing the format holds is strictly between -/
  closest : ∀ z, ReprQ fmt z → side z q → Q.Le (Q.dist q z) (Q.dist q y) → Q.Eq z y

/-! ## 3. The predicate elaborates, and it says what it should on the EASY row:
    an exactly representable value rounds to ITSELF, under any tie rule. -/

theorem nearest_of_exact (fmt : Format) (q : Q) (tieOk : Q → Prop)
    (hq : ReprQ fmt q) (htie : tieOk q) : IsNearest fmt q q tieOk where
  repr := hq
  nearest := by
    intro z _
    -- |q - q| is 0, and every `Q.dist` is a `natAbs` over a positive
    -- denominator, hence ≥ 0.  No `ring`: this component depends on NO package
    -- (charter, dependency posture), so the cancellation is done by hand.
    have h0 : (q - q).num = 0 := by
      show q.num * (q.den : Int) + (-q.num) * (q.den : Int) = 0
      rw [Int.neg_mul, Int.add_right_neg]
    show (Q.dist q q).num * (Q.dist q z).den ≤ (Q.dist q z).num * (Q.dist q q).den
    have hz : (Q.dist q q).num = 0 := by simp [Q.dist, Q.abs, h0]
    rw [hz, Int.zero_mul]
    exact Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  tie := fun _ => htie

/-- And the directed modes agree with it: an exact value is its own rounding. -/
theorem directed_of_exact (fmt : Format) (q : Q) (side : Q → Q → Prop)
    (hq : ReprQ fmt q) (hside : side q q)
    (hanti : ∀ z, Q.Le (Q.dist q z) (Q.dist q q) → Q.Eq z q) :
    IsDirected fmt q q side where
  repr := hq
  onSide := hside
  closest := fun z _ _ h => hanti z h

end LeanModels.SoftFloat
