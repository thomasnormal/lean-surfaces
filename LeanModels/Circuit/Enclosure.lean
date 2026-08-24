import Mathlib.Tactic

/-!
# Verified rational-endpoint enclosures

Endpoints are exact `Rat` values. Their interpretation is a closed set of
reals, so there is no floating-point rounding in the proof path. The initial
automation includes ordinary interval addition/multiplication and a
dependency-aware voltage-divider enclosure.
-/

namespace LeanModels.Circuit

-- Loudness guard (autoImplicit ruling, 2026-08-24): without this a mistyped or
-- unopened name is silently auto-bound rather than reported. Verified inert
-- here -- this file binds every variable it uses -- and it is file-local.
set_option autoImplicit false

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

/-! ## Transcendental numeric certificates (family F2)

The settling examples all reduce, at their last inference, to a numeric fact
about `exp` or `log` -- `hdeadline`, `hsmall` -- which reached the top of every
one of them as an UNDISCHARGED hypothesis.  `DramBankCoreSpec.lean` proved one
such constant by hand in seven bespoke lines.

These four lemmas make it a DECISION PROCEDURE instead: pick a split depth `n`,
and what remains is a rational inequality `norm_num` settles.  Nothing here is
specific to a circuit, and nothing here rounds -- the bounds come from
`Real.add_one_le_exp` and its mirror, so both endpoints are exact rationals.

The split is what makes the procedure COMPLETE rather than merely sound: the
one-step bound `exp (-a) <= 1/(1+a)` is far too weak for a real deadline, and
raising the split depth tightens it without bound.
-/

/-- One step: `exp (-a) <= 1/(1+a)` for `0 <= a`. -/
theorem exp_neg_le_inv_one_add {a : ℝ} (ha : 0 ≤ a) :
    Real.exp (-a) ≤ (1 + a)⁻¹ := by
  have hpos : (0:ℝ) < 1 + a := by linarith
  have hle : 1 + a ≤ Real.exp a := by linarith [Real.add_one_le_exp a]
  rw [Real.exp_neg]
  simpa [one_div] using one_div_le_one_div_of_le hpos hle

/-- `n`-fold split, upper side: `exp (-a) <= (1/(1+a/n))^n`. -/
theorem exp_neg_le_inv_pow {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (hn : 0 < n) :
    Real.exp (-a) ≤ ((1 + a / n)⁻¹) ^ n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hsplit : Real.exp (-a) = (Real.exp (-(a / n))) ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  rw [hsplit]
  exact pow_le_pow_left₀ (Real.exp_pos _).le
    (exp_neg_le_inv_one_add (by positivity)) n

/-- `n`-fold split, lower side: `(1 - a/n)^n <= exp (-a)` while `a <= n`.
Together with the previous lemma this is a two-sided ENCLOSURE, which is what
makes it usable where a bound alone would not be. -/
theorem one_sub_div_pow_le_exp_neg {a : ℝ} (n : ℕ) (hn : 0 < n)
    (hle : a ≤ n) : (1 - a / n) ^ n ≤ Real.exp (-a) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hsplit : Real.exp (-a) = (Real.exp (-(a / n))) ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  rw [hsplit]
  have hnn : (0:ℝ) ≤ 1 - a / n := by rw [sub_nonneg, div_le_one hn']; exact hle
  exact pow_le_pow_left₀ hnn (Real.one_sub_le_exp_neg (a / n)) n

/-- `n`-fold split on the positive side: `(1 + a/n)^n <= exp a`. -/
theorem one_add_div_pow_le_exp {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (hn : 0 < n) :
    (1 + a / n) ^ n ≤ Real.exp a := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hsplit : Real.exp a = (Real.exp (a / n)) ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  rw [hsplit]
  exact pow_le_pow_left₀ (by positivity)
    (by linarith [Real.add_one_le_exp (a / n)]) n

/-- DECAY CERTIFICATE: bound `exp (-a)` above by `b`.  Supply a split depth;
`norm_num` decides the rest. -/
theorem exp_neg_le_of_pow_le {a b : ℝ} (ha : 0 ≤ a) (n : ℕ) (hn : 0 < n)
    (h : ((1 + a / n)⁻¹) ^ n ≤ b) : Real.exp (-a) ≤ b :=
  le_trans (exp_neg_le_inv_pow ha n hn) h

/-- DEADLINE CERTIFICATE: bound `log q` above by `y`.  This is the shape the
settling theorems need, because a settling deadline is stated as a `log`. -/
theorem log_le_of_le_pow {q y : ℝ} (hq : 0 < q) (hy : 0 ≤ y)
    (n : ℕ) (hn : 0 < n) (h : q ≤ (1 + y / n) ^ n) : Real.log q ≤ y :=
  (Real.log_le_iff_le_exp hq).2 (le_trans h (one_add_div_pow_le_exp hy n hn))

/-! ### The fourth direction: growth bounded ABOVE

The three lemmas above bound decay above, decay below, and growth below --
which is everything a SETTLING circuit needs.  A regenerating one needs the
fourth: a sense amplifier's small-signal deviation GROWS, and the hypothesis
that keeps its linearisation honest is an upper bound on that growth.

The gap was found by auditing a deck's free coordinates before attempting any
proof, not by a proof failing.
-/

/-- GROWTH CERTIFICATE: `exp a ≤ (1/(1 - a/n))^n` for `a < n`. -/
theorem exp_le_inv_sub_pow {a : ℝ} (n : ℕ) (hn : 0 < n) (hlt : a < n) :
    Real.exp a ≤ ((1 - a / n)⁻¹) ^ n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hbase : (0:ℝ) < 1 - a / n := by
    rw [sub_pos, div_lt_one hn']; exact hlt
  have hlow : (1 - a / n) ^ n ≤ Real.exp (-a) :=
    one_sub_div_pow_le_exp_neg n hn hlt.le
  have hpow : (0:ℝ) < (1 - a / n) ^ n := pow_pos hbase n
  rw [inv_pow, Real.exp_neg] at *
  exact le_inv_of_le_inv₀ hpow hlow

/-- To bound `exp a` above by `b`: pick a split depth; `norm_num` the rest. -/
theorem exp_le_of_pow_le {a b : ℝ} (n : ℕ) (hn : 0 < n) (hlt : a < n)
    (h : ((1 - a / n)⁻¹) ^ n ≤ b) : Real.exp a ≤ b :=
  le_trans (exp_le_inv_sub_pow n hn hlt) h

end LeanModels.Circuit
