import Mathlib.Tactic

/-!
# Verified rational-endpoint enclosures

Endpoints are exact `Rat` values. Their interpretation is a closed set of
reals, so there is no floating-point rounding in the proof path. The initial
automation includes ordinary interval addition/multiplication and a
dependency-aware voltage-divider enclosure.
-/

namespace LeanModels.Circuit

structure RatInterval where
  lower : Rat
  upper : Rat
deriving Repr, BEq, DecidableEq, Inhabited

def RatInterval.Contains (interval : RatInterval) (value : ℝ) : Prop :=
  (interval.lower : ℝ) ≤ value ∧ value ≤ (interval.upper : ℝ)

def RatInterval.WellFormed (interval : RatInterval) : Prop :=
  interval.lower ≤ interval.upper

def RatInterval.Nonnegative (interval : RatInterval) : Prop :=
  0 ≤ interval.lower

def RatInterval.StrictlyPositive (interval : RatInterval) : Prop :=
  0 < interval.lower

def RatInterval.add (left right : RatInterval) : RatInterval :=
  ⟨left.lower + right.lower, left.upper + right.upper⟩

def RatInterval.mulNonnegative
    (left right : RatInterval) : RatInterval :=
  ⟨left.lower * right.lower, left.upper * right.upper⟩

theorem RatInterval.add_contains
    {left right : RatInterval} {x y : ℝ}
    (hleft : left.Contains x) (hright : right.Contains y) :
    (left.add right).Contains (x + y) := by
  rcases hleft with ⟨hxl, hxu⟩
  rcases hright with ⟨hyl, hyu⟩
  simp only [Contains, add, Rat.cast_add]
  constructor <;> linarith

theorem RatInterval.mulNonnegative_contains
    {left right : RatInterval} {x y : ℝ}
    (hleft : left.Contains x) (hright : right.Contains y)
    (hleftNonnegative : left.Nonnegative)
    (hrightNonnegative : right.Nonnegative) :
    (left.mulNonnegative right).Contains (x * y) := by
  rcases hleft with ⟨hxl, hxu⟩
  rcases hright with ⟨hyl, hyu⟩
  have hx : 0 ≤ x := by
    exact le_trans (by exact_mod_cast hleftNonnegative) hxl
  have hy : 0 ≤ y := by
    exact le_trans (by exact_mod_cast hrightNonnegative) hyl
  simp only [Contains, mulNonnegative, Rat.cast_mul]
  exact ⟨mul_le_mul hxl hyl (by exact_mod_cast hrightNonnegative) hx,
    mul_le_mul hxu hyu hy (le_trans hx hxu)⟩

/-- Tight independent-corner enclosure for
`supply * bottom / (top + bottom)`.

The ratio is decreasing in `top` and increasing in `bottom`, so this is
tighter than naively interval-evaluating the shared `bottom` occurrence. -/
def dividerOutputInterval
    (supply top bottom : RatInterval) : RatInterval :=
  {
    lower := supply.lower * bottom.lower / (top.upper + bottom.lower)
    upper := supply.upper * bottom.upper / (top.lower + bottom.upper) }

theorem dividerOutputInterval_contains
    {supply top bottom : RatInterval}
    {source topResistance bottomResistance : ℝ}
    (hsupplyWellFormed : supply.WellFormed)
    (htopWellFormed : top.WellFormed)
    (hbottomWellFormed : bottom.WellFormed)
    (hsupplyNonnegative : supply.Nonnegative)
    (htopPositive : top.StrictlyPositive)
    (hbottomPositive : bottom.StrictlyPositive)
    (hsupply : supply.Contains source)
    (htop : top.Contains topResistance)
    (hbottom : bottom.Contains bottomResistance) :
    (dividerOutputInterval supply top bottom).Contains
      (source * bottomResistance / (topResistance + bottomResistance)) := by
  rcases hsupply with ⟨hsourceMin, hsourceMax⟩
  rcases htop with ⟨htopMin, htopMax⟩
  rcases hbottom with ⟨hbottomMin, hbottomMax⟩
  have hsupplyLowerNonnegative : (0 : ℝ) ≤ supply.lower := by
    exact_mod_cast hsupplyNonnegative
  have htopLowerPositive : (0 : ℝ) < top.lower := by
    exact_mod_cast htopPositive
  have hbottomLowerPositive : (0 : ℝ) < bottom.lower := by
    exact_mod_cast hbottomPositive
  have hsourceNonnegative : 0 ≤ source :=
    le_trans hsupplyLowerNonnegative hsourceMin
  have htopResistancePositive : 0 < topResistance :=
    lt_of_lt_of_le htopLowerPositive htopMin
  have hbottomResistancePositive : 0 < bottomResistance :=
    lt_of_lt_of_le hbottomLowerPositive hbottomMin
  have hsumPositive : 0 < topResistance + bottomResistance :=
    add_pos htopResistancePositive hbottomResistancePositive
  have hlowerDenominator :
      0 < (top.upper : ℝ) + bottom.lower := by
    have htopUpperPositive : (0 : ℝ) < top.upper := by
      have : (top.lower : ℝ) ≤ top.upper := by
        exact_mod_cast htopWellFormed
      exact lt_of_lt_of_le htopLowerPositive this
    exact add_pos htopUpperPositive hbottomLowerPositive
  have hupperDenominator :
      0 < (top.lower : ℝ) + bottom.upper := by
    have hbottomUpperPositive : (0 : ℝ) < bottom.upper := by
      have : (bottom.lower : ℝ) ≤ bottom.upper := by
        exact_mod_cast hbottomWellFormed
      exact lt_of_lt_of_le hbottomLowerPositive this
    exact add_pos htopLowerPositive hbottomUpperPositive
  have hratioNonnegative :
      0 ≤ bottomResistance / (topResistance + bottomResistance) :=
    div_nonneg (le_of_lt hbottomResistancePositive) (le_of_lt hsumPositive)
  have hratioLow :
      (bottom.lower : ℝ) / ((top.upper : ℝ) + bottom.lower) ≤
        bottomResistance / (topResistance + bottomResistance) := by
    rw [div_le_div_iff₀ hlowerDenominator hsumPositive]
    have htopProduct :=
      mul_le_mul_of_nonneg_left htopMax
        (show (0 : ℝ) ≤ bottom.lower by
          exact le_of_lt hbottomLowerPositive)
    have hbottomProduct :=
      mul_le_mul_of_nonneg_right hbottomMin
        (show (0 : ℝ) ≤ top.upper by
          linarith)
    nlinarith
  have hratioHigh :
      bottomResistance / (topResistance + bottomResistance) ≤
        (bottom.upper : ℝ) / ((top.lower : ℝ) + bottom.upper) := by
    rw [div_le_div_iff₀ hsumPositive hupperDenominator]
    have hbottomProduct :=
      mul_le_mul_of_nonneg_right hbottomMax
        (show (0 : ℝ) ≤ top.lower by
          exact le_of_lt htopLowerPositive)
    have htopProduct :=
      mul_le_mul_of_nonneg_left htopMin
        (show (0 : ℝ) ≤ bottom.upper by
          linarith)
    nlinarith
  simp only [RatInterval.Contains, dividerOutputInterval, Rat.cast_div,
    Rat.cast_mul, Rat.cast_add]
  constructor
  · calc
      (supply.lower : ℝ) * bottom.lower /
          ((top.upper : ℝ) + bottom.lower) =
        (supply.lower : ℝ) *
          ((bottom.lower : ℝ) /
            ((top.upper : ℝ) + bottom.lower)) := by
              rw [mul_div_assoc]
      _ ≤ source *
          (bottomResistance / (topResistance + bottomResistance)) :=
        mul_le_mul hsourceMin hratioLow
          (div_nonneg (le_of_lt hbottomLowerPositive)
            (le_of_lt hlowerDenominator))
          hsourceNonnegative
      _ = source * bottomResistance /
          (topResistance + bottomResistance) := by
        rw [mul_div_assoc]
  · calc
      source * bottomResistance /
          (topResistance + bottomResistance) =
        source *
          (bottomResistance / (topResistance + bottomResistance)) := by
        rw [mul_div_assoc]
      _ ≤ (supply.upper : ℝ) *
          ((bottom.upper : ℝ) /
            ((top.lower : ℝ) + bottom.upper)) :=
        mul_le_mul hsourceMax hratioHigh hratioNonnegative
          (by
            have : (supply.lower : ℝ) ≤ supply.upper := by
              exact_mod_cast hsupplyWellFormed
            exact le_trans hsupplyLowerNonnegative this)
      _ = (supply.upper : ℝ) * bottom.upper /
          ((top.lower : ℝ) + bottom.upper) := by
        rw [mul_div_assoc]

namespace CircuitEncloseTactic

open Lean Elab Tactic

private def run : TacticM Unit := do
  evalTactic (← `(tactic|
    apply dividerOutputInterval_contains (source := _) (topResistance := _)
      (bottomResistance := _) <;>
      first
      | assumption
      | decide
      | norm_num [RatInterval.WellFormed, RatInterval.Nonnegative,
          RatInterval.StrictlyPositive]))

end CircuitEncloseTactic

open Lean Elab Tactic in
/-- Close a divider enclosure goal using the verified rational interval
procedure. The formula argument is retained in the surface because callers
normally rewrite a physical circuit behavior to the divider expression
immediately before invoking the tactic. -/
elab "circuit_enclose" "[" formula:term "]" : tactic => do
  withMainContext do
    evalTactic (← `(tactic| rw [$formula:term]))
    CircuitEncloseTactic.run

open Lean Elab Tactic in
elab "circuit_enclose" "[" formula:term "]" " with "
    "[" extras:term,* "]" : tactic => do
  withMainContext do
    let mut lemmas : TSyntaxArray ``Parser.Tactic.simpLemma := #[]
    for extra in extras.getElems do
      lemmas := lemmas.push
        (← `(Parser.Tactic.simpLemma| $extra:term))
    lemmas := lemmas.push
      (← `(Parser.Tactic.simpLemma| RatInterval.WellFormed))
    lemmas := lemmas.push
      (← `(Parser.Tactic.simpLemma| RatInterval.Nonnegative))
    lemmas := lemmas.push
      (← `(Parser.Tactic.simpLemma| RatInterval.StrictlyPositive))
    evalTactic (← `(tactic| rw [$formula:term]))
    evalTactic (← `(tactic|
      apply dividerOutputInterval_contains (source := _)
        (topResistance := _) (bottomResistance := _)))
    evalTactic (← `(tactic|
      all_goals first
        | assumption
        | norm_num [$lemmas,*]))

end LeanModels.Circuit
