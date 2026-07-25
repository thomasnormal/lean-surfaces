import Mathlib.Tactic
import LeanModels.Circuit

/-!
# Robust real-valued DC divider semantics

The exact rational SPICE solver remains a separate capability.  This module
checks that an extracted netlist has divider topology, then interprets
fabricated resistance and supply values over `ℝ` for robust assurance.
-/

namespace LeanModels.Spice

open LeanModels.Circuit

/-- Nominal divider data recovered from a literal extracted SPICE netlist. -/
structure DividerNominal where
  sourceName : String
  topName : String
  bottomName : String
  inputNode : String
  outputNode : String
  supply : Rat
  topResistance : Rat
  bottomResistance : Rat
deriving Repr, BEq

/-- Resistance values fixed for one fabricated divider instance. -/
structure DividerInstance where
  topResistance : ℝ
  bottomResistance : ℝ

/-- Exogenous supply for one DC run. -/
structure DividerEnvironment where
  supply : ℝ

/-- Observable node voltages. -/
structure DividerBoundary where
  inputVoltage : ℝ
  outputVoltage : ℝ

/-- Oriented currents through the two resistors. -/
structure DividerInternal where
  topCurrent : ℝ
  bottomCurrent : ℝ

abbrev DividerWorld :=
  RunWorld DividerInstance DividerEnvironment Unit Unit

/-- Ohm's law for each resistor, the source law, and KCL at the output.
No closed-form divider equation is assumed. -/
def DividerBehavior :
    Behavior DividerWorld DividerBoundary DividerInternal :=
  fun world boundary internal =>
    boundary.inputVoltage = world.environment.supply ∧
    internal.topCurrent =
      (boundary.inputVoltage - boundary.outputVoltage) /
        world.fabricated.topResistance ∧
    internal.bottomCurrent =
      boundary.outputVoltage / world.fabricated.bottomResistance ∧
    internal.topCurrent = internal.bottomCurrent

/-- General correlated admissible sets are predicates over the whole world.
This box is the concrete set used by the example. -/
structure DividerBounds where
  supplyMin : ℝ
  supplyMax : ℝ
  topMin : ℝ
  topMax : ℝ
  bottomMin : ℝ
  bottomMax : ℝ

def DividerBounds.Admissible (bounds : DividerBounds)
    (world : DividerWorld) : Prop :=
  bounds.supplyMin ≤ world.environment.supply ∧
  world.environment.supply ≤ bounds.supplyMax ∧
  bounds.topMin ≤ world.fabricated.topResistance ∧
  world.fabricated.topResistance ≤ bounds.topMax ∧
  bounds.bottomMin ≤ world.fabricated.bottomResistance ∧
  world.fabricated.bottomResistance ≤ bounds.bottomMax

def DividerPositive (world : DividerWorld) : Prop :=
  0 < world.fabricated.topResistance ∧
  0 < world.fabricated.bottomResistance

/-- The closed form is derived from the relational physical laws. -/
theorem divider_output_eq
    {world : DividerWorld} {boundary : DividerBoundary}
    {internal : DividerInternal}
    (hpositive : DividerPositive world)
    (hbehavior : DividerBehavior world boundary internal) :
    boundary.outputVoltage =
      world.environment.supply * world.fabricated.bottomResistance /
        (world.fabricated.topResistance +
          world.fabricated.bottomResistance) := by
  rcases hbehavior with ⟨hinput, htop, hbottom, hkcl⟩
  rw [htop, hbottom, hinput] at hkcl
  have htop0 : world.fabricated.topResistance ≠ 0 := ne_of_gt hpositive.1
  have hbottom0 : world.fabricated.bottomResistance ≠ 0 :=
    ne_of_gt hpositive.2
  have hsum0 :
      world.fabricated.topResistance +
        world.fabricated.bottomResistance ≠ 0 := by
    exact ne_of_gt (add_pos hpositive.1 hpositive.2)
  field_simp [htop0, hbottom0] at hkcl
  apply (eq_div_iff hsum0).2
  nlinarith

/-- Positive-resistance divider states always exist; this is the
non-vacuity half of the model. -/
theorem divider_realizable :
    RealizableUnder DividerBehavior DividerPositive := by
  intro world hpositive
  let total :=
    world.fabricated.topResistance + world.fabricated.bottomResistance
  let output :=
    world.environment.supply * world.fabricated.bottomResistance / total
  let current := world.environment.supply / total
  refine ⟨⟨world.environment.supply, output⟩, ⟨current, current⟩, ?_⟩
  have htop0 : world.fabricated.topResistance ≠ 0 := ne_of_gt hpositive.1
  have hbottom0 : world.fabricated.bottomResistance ≠ 0 :=
    ne_of_gt hpositive.2
  have htotal0 : total ≠ 0 := by
    dsimp [total]
    exact ne_of_gt (add_pos hpositive.1 hpositive.2)
  constructor
  · rfl
  constructor
  · dsimp [output, current, total]
    have hsum0 :
        world.fabricated.topResistance +
          world.fabricated.bottomResistance ≠ 0 :=
      ne_of_gt (add_pos hpositive.1 hpositive.2)
    field_simp [htop0, hsum0]
    ring
  constructor
  · dsimp [output, current, total]
    field_simp [htop0, hbottom0, htotal0]
  · rfl

/-- The output observation is unique even though the denotation is relational. -/
theorem divider_output_determinate :
    DeterminateUnder DividerBehavior DividerPositive ℝ
      (fun _world boundary _internal => boundary.outputVoltage) := by
  intro world hpositive boundary₁ internal₁ boundary₂ internal₂
      hbehavior₁ hbehavior₂
  change boundary₁.outputVoltage = boundary₂.outputVoltage
  rw [divider_output_eq hpositive hbehavior₁,
    divider_output_eq hpositive hbehavior₂]

/-- A simple voltage validity domain for divider model evidence. -/
def DividerVoltageDomain (maximum : ℝ)
    (_world : DividerWorld) (boundary : DividerBoundary)
    (_internal : DividerInternal) : Prop :=
  0 ≤ boundary.inputVoltage ∧ boundary.inputVoltage ≤ maximum ∧
  0 ≤ boundary.outputVoltage ∧ boundary.outputVoltage ≤ maximum

/-- With a nonnegative bounded supply and positive resistors, every divider
behavior remains within the same voltage envelope. -/
theorem divider_stays_in_voltage_domain (maximum : ℝ) :
    StaysWithinValidityDomain DividerBehavior
      (fun world =>
        DividerPositive world ∧
        0 ≤ world.environment.supply ∧
        world.environment.supply ≤ maximum)
      (DividerVoltageDomain maximum) := by
  intro world boundary internal hallowed hbehavior
  have hformula := divider_output_eq hallowed.1 hbehavior
  have htop : 0 < world.fabricated.topResistance := hallowed.1.1
  have hbottom : 0 < world.fabricated.bottomResistance := hallowed.1.2
  have hsum :
      0 < world.fabricated.topResistance +
        world.fabricated.bottomResistance := by positivity
  have hratio0 :
      0 ≤ world.fabricated.bottomResistance /
        (world.fabricated.topResistance +
          world.fabricated.bottomResistance) := by positivity
  have hratio1 :
      world.fabricated.bottomResistance /
          (world.fabricated.topResistance +
            world.fabricated.bottomResistance) ≤ 1 := by
    rw [div_le_one hsum]
    linarith
  rcases hbehavior with ⟨hinput, _⟩
  constructor
  · simpa [hinput] using hallowed.2.1
  constructor
  · simpa [hinput] using hallowed.2.2
  constructor
  · rw [hformula, mul_div_assoc]
    exact mul_nonneg hallowed.2.1 hratio0
  · rw [hformula, mul_div_assoc]
    calc
      world.environment.supply *
          (world.fabricated.bottomResistance /
            (world.fabricated.topResistance +
              world.fabricated.bottomResistance))
          ≤ world.environment.supply * 1 :=
        mul_le_mul_of_nonneg_left hratio1 hallowed.2.1
      _ ≤ maximum := by simpa using hallowed.2.2

end LeanModels.Spice
