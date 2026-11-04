/-
# SoftFloat, layer 2 — MULTIPLICATION, reduced to one obligation

IEEE 754-2019 §5.4.1.  The first arithmetic `op_correct`, and it is stated
against `Round.lean`'s DECLARATIVE spec — `IsNearest` / `TieEven` — never
against `RoundAlg.lean`'s `roundQ`.  No implementation appears on either side
of the conclusion, which is the whole anti-circularity argument (charter
§3.5.2).

WHY `×` AND NOT `+`, measured from core's code rather than chosen:
`mul`'s finite branch is ONE line — `roundWithAccuracy fmt (s₁*s₂) (m₁*m₂)
(e₁+e₂) .exact` — the exact product's significand and exponent handed straight
to rounding.  `add` first aligns exponents with two `decreaseExponent` calls,
forms a SIGNED sum that can be negative or zero, then calls `normalize`, which
case-splits three ways on the sign and calls `round`, which calls
`roundWithAccuracy` anyway.  **`mul`'s obligation is a strict sub-problem of
`add`'s.**

AND THE REDUCTION MEASURES THAT CLAIM.  `mul_correct_of`'s proof is a SINGLE
TERM APPLICATION — no tactics, no case analysis, no arithmetic beyond
`Nat.mul_pos`.  Multiplication's entire content **beyond the rounding lemma is
nothing**.  That is the sub-problem ordering, confirmed rather than asserted.
-/
import LeanModels.SoftFloat.Round

namespace LeanModels.SoftFloat

open Float.Model
open Float.Model.UnpackedFloat (Sign)

/-- The exact product of two finite floats is a DYADIC — no division, no ℝ. -/
abbrev exactMul (s₁ s₂ : Sign) (m₁ m₂ : Nat) (e₁ e₂ : Int) : Q :=
  Q.dyadic ((s₁ * s₂).apply (m₁ * m₂ : Nat)) (e₁ + e₂)

/--
THE ONE OBLIGATION `mul_correct` NEEDS, carried as a hypothesis so that it is
**type-checked rather than described**: core's `roundWithAccuracy`, on an input
flagged `.exact`, yields the correctly-rounded value of that input.

It is a statement about **core's** rounding, not about this component's
`roundQ` — see the note on `mul_correct_of`.
-/
abbrev RoundWithAccuracyIsNearest : Prop :=
  ∀ (fmt : Format) (s : Sign) (m : Nat) (e : Int) (q : Q),
    0 < m →
    valQ (UnpackedFloat.roundWithAccuracy fmt s m e .exact) = some q →
    IsNearest fmt (Q.dyadic (s.apply (m : Nat)) e) q (TieEven fmt)

/--
IEEE 754-2019 §5.4.1, REDUCED: multiplication returns the correctly-rounded
exact product, **provided** core's exact-input rounding is correctly rounded.

THREE THINGS THIS SHAPE BUYS.

1. **No `sorry`.** The residual obligation is a HYPOTHESIS, so this file carries
   no `sorryAx` and its axiom print stays readable — `mul_correct_of` depends
   on **no axioms at all**.  A `sorry`ed `mul_correct` would have poisoned the
   receipts of every theorem beside it (§0.1 II(a)).
2. **No overflow hypothesis is needed**, and that is the §7.4 omission in
   `ReprQ` paying off: `ReprQ` deliberately carries no UPPER exponent bound, so
   an overflowed result is still representable by it and the theorem holds
   unconditionally on finite inputs.  Overflow is a separate clause with a
   mode-dependent answer, and keeping it out kept this statement clean.
3. **`roundQ` is not on this path.** The obligation names core's
   `roundWithAccuracy`.  This component's `roundQ` would only be needed to state
   `mul = roundQ (exact …)`, which is precisely the circular form §3.5.2 warns
   against.  `roundQ` is a PARALLEL artifact, not a prerequisite.
-/
theorem mul_correct_of (H : RoundWithAccuracyIsNearest)
    (fmt : Format) (s₁ s₂ : Sign) (m₁ m₂ : Nat) (e₁ e₂ : Int)
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) (qr : Q)
    (hr : valQ (UnpackedFloat.mul fmt (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂)) = some qr) :
    IsNearest fmt (exactMul s₁ s₂ m₁ m₂ e₁ e₂) qr (TieEven fmt) :=
  H fmt (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) qr (Nat.mul_pos h₁ h₂) hr

/-- `mul` on two finites IS `roundWithAccuracy` of the exact product — the
    structural fact the reduction rests on, and it holds by `rfl`. -/
theorem mul_eq_roundWithAccuracy (fmt : Format) (s₁ s₂ : Sign)
    (m₁ m₂ : Nat) (e₁ e₂ : Int) (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    UnpackedFloat.mul fmt (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂)
      = UnpackedFloat.roundWithAccuracy fmt (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) .exact := rfl

#print axioms mul_correct_of
#print axioms mul_eq_roundWithAccuracy

end LeanModels.SoftFloat
