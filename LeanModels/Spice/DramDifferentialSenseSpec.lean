import LeanModels.Spice.DramDifferentialSense

/-!
# Differential sense-amplifier specifications

Specifications are deliberately downstream of the primitive equation module.
The equation module proves source projection, physical equilibria,
finite-horizon realizability, determinacy, and rail-domain invariance for
every balanced scalar trajectory across all three nominal MOS regions. This
module adds observation predicates and the exact first-region margin
deadline. The equation module also proves that every rail-valid primitive
two-node trajectory with balanced initial data remains balanced and projects
exactly into that scalar view. Unconditional vector rail-domain invariance,
unbalanced or mismatched trajectories, offset coverage, and global
quantitative settling remain separate obligations and are not assumed by the
physics.
-/

namespace LeanModels.Spice

open LeanModels.Circuit

def DramDifferentialSenseInitialMargin
    (world : DramDifferentialSenseWorld)
    (value : Bool) (offset required : ℝ) : Prop :=
  0 ≤ offset ∧ 0 < required ∧
    if value then
      offset + required ≤
        world.environment.initialTrue -
          world.environment.initialComplement
    else
      offset + required ≤
        world.environment.initialComplement -
          world.environment.initialTrue

def DramDifferentialSenseResolved
    (world : DramDifferentialSenseWorld)
    (boundary : DramDifferentialSenseBoundary)
    (value : Bool) : Prop :=
  boundary.voltage world.environment.horizon =
    dramDifferentialSenseRailState world.environment.supply value

def DramDifferentialSenseInRailDomain
    (world : DramDifferentialSenseWorld)
    (boundary : DramDifferentialSenseBoundary) : Prop :=
  ∀ time, 0 ≤ time → time ≤ world.environment.horizon →
    0 ≤ boundary.voltage time .trueLine ∧
    boundary.voltage time .trueLine ≤ world.environment.supply ∧
    0 ≤ boundary.voltage time .complementLine ∧
    boundary.voltage time .complementLine ≤ world.environment.supply

/-- Signed half-differential observed in the direction of the selected
logical value. -/
noncomputable def DramDifferentialSenseDeviation
    (boundary : DramDifferentialSenseBoundary)
    (value : Bool) (time : ℝ) : ℝ :=
  if value then
    (boundary.voltage time .trueLine -
      boundary.voltage time .complementLine) / 2
  else
    (boundary.voltage time .complementLine -
      boundary.voltage time .trueLine) / 2

/-- The latch has amplified its input to at least `required` differential
deviation by `deadline`, and retains that margin for the requested horizon. -/
def DramDifferentialSenseReachesMargin
    (world : DramDifferentialSenseWorld)
    (boundary : DramDifferentialSenseBoundary)
    (value : Bool) (required deadline : ℝ) : Prop :=
  0 ≤ required ∧ 0 ≤ deadline ∧
    deadline ≤ world.environment.horizon ∧
    ∀ time, deadline ≤ time →
      time ≤ world.environment.horizon →
      required ≤
        DramDifferentialSenseDeviation boundary value time

/-- Nonnegative logarithmic deadline for the exact first-region trajectory. -/
noncomputable def dramDifferentialSenseSmallSignalDeadline
    (initialDeviation required : ℝ) : ℝ :=
  max 0
    (Real.log (required / initialDeviation) / 1000000000)

/-- The explicit source-backed small-signal witness stays inside the physical
rail domain throughout every horizon on which it remains in the first MOS
region. -/
theorem dramDifferentialSense_small_signal_witness_in_domain
    {world : DramDifferentialSenseWorld}
    {initialDeviation : ℝ}
    (hsupply : world.environment.supply = 5)
    (hinitial : 0 ≤ initialDeviation)
    (hsmall :
      dramDifferentialSenseSmallSignalTrace initialDeviation
          world.environment.horizon ≤
        1 / 2) :
    DramDifferentialSenseInRailDomain world
      (dramDifferentialSenseSmallSignalBoundary
        world initialDeviation) := by
  intro time htime0 htimeH
  have hdeviation0 :=
    dramDifferentialSenseSmallSignalTrace_nonnegative
      (time := time) hinitial
  have hdeviationSmall :
      dramDifferentialSenseSmallSignalTrace initialDeviation time ≤
        1 / 2 :=
    (dramDifferentialSenseSmallSignalTrace_le_horizon
      hinitial htimeH).trans hsmall
  simp only [dramDifferentialSenseSmallSignalBoundary,
    dramDifferentialSenseBalancedTrace,
    dramDifferentialSenseBalancedState]
  rw [hsupply]
  exact
    ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- The same witness reaches any requested positive first-region margin by
the source-derived logarithmic deadline. -/
theorem dramDifferentialSense_small_signal_witness_reaches_margin
    {world : DramDifferentialSenseWorld}
    {initialDeviation required : ℝ}
    (hinitial : 0 < initialDeviation)
    (hrequired : 0 < required)
    (hdeadline :
      dramDifferentialSenseSmallSignalDeadline
          initialDeviation required ≤
        world.environment.horizon) :
    DramDifferentialSenseReachesMargin world
      (dramDifferentialSenseSmallSignalBoundary
        world initialDeviation)
      true required
      (dramDifferentialSenseSmallSignalDeadline
        initialDeviation required) := by
  refine
    ⟨hrequired.le,
      le_max_left _ _,
      hdeadline, ?_⟩
  intro time htimeDeadline _htimeH
  have htime :
      Real.log (required / initialDeviation) / 1000000000 ≤
        time :=
    (le_max_right 0 _).trans htimeDeadline
  have hreaches :=
    dramDifferentialSenseSmallSignalTrace_reaches
      hinitial hrequired htime
  simpa [DramDifferentialSenseDeviation,
    dramDifferentialSenseSmallSignalBoundary,
    dramDifferentialSenseBalancedTrace,
    dramDifferentialSenseBalancedState] using hreaches

/-- A rail-equilibrium witness is resolved correctly. This is an endpoint
fact about the exhibited physical behavior, not a claim that every
margin-separated initial state has already been proved to converge. -/
theorem dramDifferentialSense_rail_witness_resolved
    (world : DramDifferentialSenseWorld) (value : Bool) :
    DramDifferentialSenseResolved world
      ⟨fun _time =>
        dramDifferentialSenseRailState world.environment.supply value⟩
      value := by
  rfl

theorem dramDifferentialSense_rail_witness_in_domain
    {world : DramDifferentialSenseWorld}
    (hsupply : 0 ≤ world.environment.supply)
    (value : Bool) :
    DramDifferentialSenseInRailDomain world
      ⟨fun _time =>
        dramDifferentialSenseRailState world.environment.supply value⟩ := by
  intro time _htime0 _htimeH
  cases value <;>
    simp [dramDifferentialSenseRailState, hsupply]

/-- The physical model explicitly admits a midpoint behavior; positive-rail
resolution therefore cannot be concluded without a nonzero input-margin and
dynamic basin argument. -/
theorem dramDifferentialSense_metastable_not_resolved
    {world : DramDifferentialSenseWorld}
    (hsupply : 0 < world.environment.supply)
    (value : Bool) :
    ¬ DramDifferentialSenseResolved world
      ⟨fun _time =>
        dramDifferentialSenseMetastableState world.environment.supply⟩
      value := by
  intro hresolved
  have hpoint :=
    congrFun hresolved DramDifferentialSenseIndex.trueLine
  cases value <;>
    simp [dramDifferentialSenseMetastableState,
      dramDifferentialSenseRailState] at hpoint <;>
    linarith

end LeanModels.Spice
