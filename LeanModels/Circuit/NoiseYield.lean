import Mathlib.Tactic

/-!
# Bounded noise and finite probabilistic yield

Worst-case disturbance and probabilistic yield are deliberately different
objects. `FiniteDistribution` is an exact, auditable distribution over whole
worlds; it does not resample process parameters at each equation or time.
-/

namespace LeanModels.Circuit

def BoundedNoise (radius noise : ℝ) : Prop :=
  |noise| ≤ radius

/-- An additive bounded observation widens a proved interval by its radius. -/
theorem bounded_noise_widens_interval
    {lower nominal upper radius noise : ℝ}
    (_hradius : 0 ≤ radius)
    (hnominal : lower ≤ nominal ∧ nominal ≤ upper)
    (hnoise : BoundedNoise radius noise) :
    lower - radius ≤ nominal + noise ∧
      nominal + noise ≤ upper + radius := by
  rw [BoundedNoise, abs_le] at hnoise
  constructor <;> linarith

/-- A finite exact probability distribution. Correlated quantities live
inside one outcome and are selected together. -/
structure FiniteDistribution (α : Type) where
  outcomes : List (α × ℝ)
  weight_nonnegative :
    ∀ outcome weight, (outcome, weight) ∈ outcomes → 0 ≤ weight
  total_weight : (outcomes.map Prod.snd).sum = 1

/-- Every positive-probability outcome satisfies `property`. -/
def FiniteAlmostSure
    (distribution : FiniteDistribution α) (property : α → Prop) : Prop :=
  ∀ outcome weight, (outcome, weight) ∈ distribution.outcomes →
    0 < weight → property outcome

noncomputable def finiteYield
    (distribution : FiniteDistribution α) (property : α → Prop) : ℝ := by
  classical
  exact (distribution.outcomes.map fun entry =>
    if property entry.1 then entry.2 else 0).sum

/-- Universal proof over the distribution support produces an exact
probability-one yield theorem. -/
theorem FiniteAlmostSure.yield_eq_one
    {distribution : FiniteDistribution α} {property : α → Prop}
    (halmost : FiniteAlmostSure distribution property) :
    finiteYield distribution property = 1 := by
  classical
  unfold finiteYield
  rw [← distribution.total_weight]
  apply congrArg List.sum
  apply List.map_congr_left
  intro entry hentry
  rcases entry with ⟨outcome, weight⟩
  have hnonnegative :=
    distribution.weight_nonnegative outcome weight hentry
  by_cases hpositive : 0 < weight
  · have hproperty := halmost outcome weight hentry hpositive
    simp [hproperty]
  · have hzero : weight = 0 := by linarith
    simp [hzero]

end LeanModels.Circuit
