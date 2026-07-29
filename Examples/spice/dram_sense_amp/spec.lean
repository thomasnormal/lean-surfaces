import LeanModels.Python.Surface
import Examples.spice.dram_sense_amp.proof

open LeanModels.Circuit LeanModels.Spice
open Examples.spice.dram_sense_amp.proof

theorem dram_sense_amp_projection :
    dramSenseAmp.toDramDifferentialSense = .ok dramSenseAmpLayout := by proofs

theorem dram_sense_amp_parameters :
    dramSenseAmpLayout.fabricated =
      { nThreshold := 1
        pThreshold := 1
        nBeta := 1 / 10000
        pBeta := 1 / 10000
        trueCapacitance := 3 / 10000000000000
        complementCapacitance := 3 / 10000000000000 } := by proofs

theorem dram_sense_amp_equation_manifest :
    EquationManifest DramDifferentialSenseProgram [] := by proofs

theorem dram_sense_amp_rail_realizable (value : Bool) :
    ∃ boundary,
      DramDifferentialSenseBehavior
        (dramSenseWorld
          (if value then 5 else 0)
          (if value then 0 else 5) 1)
        boundary () := by proofs

theorem dram_sense_amp_metastable_realizable :
    ∃ boundary,
      DramDifferentialSenseBehavior
        (dramSenseWorld (5 / 2) (5 / 2) 1) boundary () := by proofs

theorem dram_sense_amp_metastable_not_resolved (value : Bool) :
    ¬ DramDifferentialSenseResolved
      (dramSenseWorld (5 / 2) (5 / 2) 1)
      ⟨fun _time =>
        dramDifferentialSenseMetastableState 5⟩ value := by proofs

theorem dram_sense_amp_local_regeneration
    {time deviation : ℝ}
    {derivative : VectorState DramDifferentialSenseIndex}
    (hdeviation : 0 < deviation)
    (hregion : deviation < 1 / 2)
    (hresidual :
      dramDifferentialSenseDAE.residual
        (dramSenseWorld (5 / 2 + deviation)
          (5 / 2 - deviation) 1)
        time (dramDifferentialSenseBalancedState 5 deviation)
        derivative) :
    0 < derivative .trueLine - derivative .complementLine := by proofs

/-- The source-backed latch initially amplifies every ordered bitline pair
inside the rail rectangle, even when its common mode is not balanced. -/
theorem dram_sense_amp_unbalanced_regeneration
    {initialTrue initialComplement horizon time : ℝ}
    {state derivative : VectorState DramDifferentialSenseIndex}
    (hstate :
      DramDifferentialSenseStateInRailDomain
        (dramSenseWorld initialTrue initialComplement horizon) state)
    (horder : state .complementLine < state .trueLine)
    (hnotRail :
      state .trueLine < 5 ∨ 0 < state .complementLine)
    (hresidual :
      dramDifferentialSenseDAE.residual
        (dramSenseWorld initialTrue initialComplement horizon)
        time state derivative) :
    0 < derivative .trueLine - derivative .complementLine := by proofs

/-- Symmetric polarity: if the complement bitline starts higher, the signed
true-minus-complement differential becomes strictly more negative. -/
theorem dram_sense_amp_unbalanced_regeneration_reverse
    {initialTrue initialComplement horizon time : ℝ}
    {state derivative : VectorState DramDifferentialSenseIndex}
    (hstate :
      DramDifferentialSenseStateInRailDomain
        (dramSenseWorld initialTrue initialComplement horizon) state)
    (horder : state .trueLine < state .complementLine)
    (hnotRail :
      state .complementLine < 5 ∨ 0 < state .trueLine)
    (hresidual :
      dramDifferentialSenseDAE.residual
        (dramSenseWorld initialTrue initialComplement horizon)
        time state derivative) :
    derivative .trueLine - derivative .complementLine < 0 := by proofs

/-- Every instantaneous state of the source-backed latch has a primitive
derivative satisfying both capacitor KCL equations. -/
theorem dram_sense_amp_unbalanced_residual_realizable
    {initialTrue initialComplement horizon time : ℝ}
    {state : VectorState DramDifferentialSenseIndex} :
    ∃ derivative : VectorState DramDifferentialSenseIndex,
      dramDifferentialSenseDAE.residual
        (dramSenseWorld initialTrue initialComplement horizon)
        time state derivative := by proofs

theorem dram_sense_amp_balanced_rate_formula
    {deviation : ℝ}
    (hdeviation0 : 0 ≤ deviation)
    (hdeviationRail : deviation ≤ 5 / 2) :
    dramDifferentialSenseBalancedRate
        (dramSenseWorld (5 / 2 + deviation)
          (5 / 2 - deviation) 1)
        deviation =
      dramDifferentialSenseNominalBalancedRate deviation := by proofs

theorem dram_sense_amp_balanced_residual_realizable
    {time deviation : ℝ} :
    ∃ derivative : VectorState DramDifferentialSenseIndex,
      dramDifferentialSenseDAE.residual
        (dramSenseWorld (5 / 2 + deviation)
          (5 / 2 - deviation) 1)
        time (dramDifferentialSenseBalancedState 5 deviation)
        derivative := by proofs

/-- Every balanced nominal initial differential in the selected basin has a
genuine primitive four-MOS/two-capacitor trajectory for every finite horizon,
and the constructed trajectory remains between the supply rails. -/
theorem dram_sense_amp_full_basin_realizable
    {initialDeviation horizon : ℝ}
    (hinitial0 : 0 ≤ initialDeviation)
    (hinitialRail : initialDeviation ≤ 5 / 2)
    (hhorizon : 0 ≤ horizon) :
    ∃ boundary,
      DramDifferentialSenseBehavior
          (dramSenseWorld
            (5 / 2 + initialDeviation)
            (5 / 2 - initialDeviation) horizon)
          boundary () ∧
        DramDifferentialSenseInRailDomain
          (dramSenseWorld
            (5 / 2 + initialDeviation)
            (5 / 2 - initialDeviation) horizon)
          boundary := by proofs

/-- The complete source-derived scalar DAE has only one finite-horizon
trajectory from a given initial differential. No rail-domain premise is
assumed. -/
theorem dram_sense_amp_full_basin_scalar_determinate
    {first second : DenseTrace ℝ}
    {initialDeviation horizon time : ℝ}
    (hfirst :
      dramDifferentialSenseBalancedDAE.ACBehavesOn
        (dramSenseWorld
          (5 / 2 + initialDeviation)
          (5 / 2 - initialDeviation) horizon)
        horizon first)
    (hsecond :
      dramDifferentialSenseBalancedDAE.ACBehavesOn
        (dramSenseWorld
          (5 / 2 + initialDeviation)
          (5 / 2 - initialDeviation) horizon)
        horizon second)
    (hinitial : first 0 = second 0)
    (htime0 : 0 ≤ time)
    (htimeHorizon : time ≤ horizon) :
    first time = second time := by proofs

/-- Every rail-valid behavior of the literal source-backed two-node circuit
preserves the balanced common mode selected by its initial conditions. -/
theorem dram_sense_amp_vector_balanced_on_domain
    {boundary : DramDifferentialSenseBoundary}
    {initialDeviation horizon time : ℝ}
    (hbehavior :
      DramDifferentialSenseBehavior
        (dramSenseWorld
          (5 / 2 + initialDeviation)
          (5 / 2 - initialDeviation) horizon)
        boundary ())
    (hdomain :
      DramDifferentialSenseInRailDomain
        (dramSenseWorld
          (5 / 2 + initialDeviation)
          (5 / 2 - initialDeviation) horizon)
        boundary)
    (htime0 : 0 ≤ time)
    (htimeHorizon : time ≤ horizon) :
    boundary.voltage time .trueLine +
        boundary.voltage time .complementLine = 5 := by proofs

/-- Every rail-valid behavior of the literal source-backed circuit projects
to the exact scalar differential-mode DAE. -/
theorem dram_sense_amp_vector_projects_to_scalar_on_domain
    {boundary : DramDifferentialSenseBoundary}
    {initialDeviation horizon : ℝ}
    (hbehavior :
      DramDifferentialSenseBehavior
        (dramSenseWorld
          (5 / 2 + initialDeviation)
          (5 / 2 - initialDeviation) horizon)
        boundary ())
    (hdomain :
      DramDifferentialSenseInRailDomain
        (dramSenseWorld
          (5 / 2 + initialDeviation)
          (5 / 2 - initialDeviation) horizon)
        boundary) :
    dramDifferentialSenseBalancedDAE.ACBehavesOn
      (dramSenseWorld
        (5 / 2 + initialDeviation)
        (5 / 2 - initialDeviation) horizon)
      horizon
      (dramDifferentialSenseTraceDeviation boundary.voltage) := by proofs

/-- The literal nominal two-node circuit has at most one rail-valid
trajectory from its source-imposed balanced initial state. -/
theorem dram_sense_amp_vector_determinate_on_domain
    {first second : DramDifferentialSenseBoundary}
    {initialDeviation horizon time : ℝ}
    (hfirst :
      DramDifferentialSenseBehavior
        (dramSenseWorld
          (5 / 2 + initialDeviation)
          (5 / 2 - initialDeviation) horizon)
        first ())
    (hsecond :
      DramDifferentialSenseBehavior
        (dramSenseWorld
          (5 / 2 + initialDeviation)
          (5 / 2 - initialDeviation) horizon)
        second ())
    (hfirstDomain :
      DramDifferentialSenseInRailDomain
        (dramSenseWorld
          (5 / 2 + initialDeviation)
          (5 / 2 - initialDeviation) horizon)
        first)
    (hsecondDomain :
      DramDifferentialSenseInRailDomain
        (dramSenseWorld
          (5 / 2 + initialDeviation)
          (5 / 2 - initialDeviation) horizon)
        second)
    (htime0 : 0 ≤ time)
    (htimeHorizon : time ≤ horizon) :
    first.voltage time = second.voltage time := by proofs

/-- Every physical scalar trajectory starting in the selected balanced basin
stays between the metastable midpoint and the selected rail. -/
theorem dram_sense_amp_full_basin_no_overshoot
    {trajectory : DenseTrace ℝ}
    {initialDeviation horizon : ℝ}
    (hbehavior :
      dramDifferentialSenseBalancedDAE.ACBehavesOn
        (dramSenseWorld
          (5 / 2 + initialDeviation)
          (5 / 2 - initialDeviation) horizon)
        horizon trajectory)
    (hinitial : trajectory 0 = initialDeviation)
    (hinitial0 : 0 ≤ initialDeviation)
    (hinitialRail : initialDeviation ≤ 5 / 2) :
    NoOvershoot trajectory 0 (5 / 2) horizon := by proofs

/-- Every physical scalar trajectory starting in the selected balanced basin
moves monotonically toward the selected rail. -/
theorem dram_sense_amp_full_basin_monotone
    {trajectory : DenseTrace ℝ}
    {initialDeviation horizon : ℝ}
    (hbehavior :
      dramDifferentialSenseBalancedDAE.ACBehavesOn
        (dramSenseWorld
          (5 / 2 + initialDeviation)
          (5 / 2 - initialDeviation) horizon)
        horizon trajectory)
    (hinitial : trajectory 0 = initialDeviation)
    (hinitial0 : 0 ≤ initialDeviation)
    (hinitialRail : initialDeviation ≤ 5 / 2) :
    MonotoneOn trajectory (Set.Icc (0 : ℝ) horizon) := by proofs

theorem dram_sense_amp_small_signal_behavior
    {initialDeviation horizon : ℝ}
    (hinitial : 0 ≤ initialDeviation)
    (hhorizon : 0 ≤ horizon)
    (hsmall :
      dramDifferentialSenseSmallSignalTrace
          initialDeviation horizon ≤
        1 / 2) :
    DramDifferentialSenseBehavior
      (dramSenseWorld
        (5 / 2 + initialDeviation)
        (5 / 2 - initialDeviation) horizon)
      (dramDifferentialSenseSmallSignalBoundary
        (dramSenseWorld
          (5 / 2 + initialDeviation)
          (5 / 2 - initialDeviation) horizon)
        initialDeviation) () := by proofs

/-- Every balanced scalar DAE trajectory that stays in the first MOS region
is the source-derived exponential trajectory. -/
theorem dram_sense_amp_small_signal_scalar_determinate
    {deviation : DenseTrace ℝ}
    {initialDeviation horizon time : ℝ}
    (hbehavior :
      dramDifferentialSenseBalancedDAE.ACBehavesOn
        (dramSenseWorld
          (5 / 2 + initialDeviation)
          (5 / 2 - initialDeviation) horizon)
        horizon deviation)
    (hinitial : deviation 0 = initialDeviation)
    (hdomain :
      ∀ point, 0 ≤ point → point ≤ horizon →
        0 ≤ deviation point ∧ deviation point ≤ 1 / 2)
    (htime0 : 0 ≤ time)
    (htimeHorizon : time ≤ horizon) :
    deviation time =
      dramDifferentialSenseSmallSignalTrace
        initialDeviation time := by proofs

theorem dram_sense_amp_small_signal_realizable
    {initialDeviation horizon : ℝ}
    (hinitial : 0 ≤ initialDeviation)
    (hhorizon : 0 ≤ horizon)
    (hsmall :
      dramDifferentialSenseSmallSignalTrace
          initialDeviation horizon ≤
        1 / 2) :
    ∃ boundary,
      DramDifferentialSenseBehavior
        (dramSenseWorld
          (5 / 2 + initialDeviation)
          (5 / 2 - initialDeviation) horizon)
        boundary () := by proofs

/-- A nonzero balanced input has a genuine source-backed transient that
stays between the supply rails and reaches any requested first-region margin
by the closed-form deadline. -/
theorem dram_sense_amp_small_signal_performance_realizable
    {initialDeviation required horizon : ℝ}
    (hinitial : 0 < initialDeviation)
    (hrequired : 0 < required)
    (hdeadline :
      dramDifferentialSenseSmallSignalDeadline
          initialDeviation required ≤ horizon)
    (hsmall :
      dramDifferentialSenseSmallSignalTrace
          initialDeviation horizon ≤
        1 / 2) :
    ∃ boundary,
      DramDifferentialSenseBehavior
          (dramSenseWorld
            (5 / 2 + initialDeviation)
            (5 / 2 - initialDeviation) horizon)
          boundary () ∧
        DramDifferentialSenseInRailDomain
          (dramSenseWorld
            (5 / 2 + initialDeviation)
            (5 / 2 - initialDeviation) horizon)
          boundary ∧
        DramDifferentialSenseReachesMargin
          (dramSenseWorld
            (5 / 2 + initialDeviation)
            (5 / 2 - initialDeviation) horizon)
          boundary true required
          (dramDifferentialSenseSmallSignalDeadline
            initialDeviation required) := by proofs

theorem dram_sense_amp_full_basin_regeneration
    {time deviation : ℝ}
    {derivative : VectorState DramDifferentialSenseIndex}
    (hdeviation : 0 < deviation)
    (hdeviationRail : deviation < 5 / 2)
    (hresidual :
      dramDifferentialSenseDAE.residual
        (dramSenseWorld (5 / 2 + deviation)
          (5 / 2 - deviation) 1)
        time (dramDifferentialSenseBalancedState 5 deviation)
        derivative) :
    0 < derivative .trueLine ∧
      derivative .complementLine < 0 ∧
      derivative .trueLine + derivative .complementLine = 0 := by proofs

#print axioms dram_sense_amp_projection
#print axioms dram_sense_amp_parameters
#print axioms dram_sense_amp_equation_manifest
#print axioms dram_sense_amp_rail_realizable
#print axioms dram_sense_amp_metastable_realizable
#print axioms dram_sense_amp_metastable_not_resolved
#print axioms dram_sense_amp_local_regeneration
#print axioms dram_sense_amp_unbalanced_regeneration
#print axioms dram_sense_amp_unbalanced_regeneration_reverse
#print axioms dram_sense_amp_unbalanced_residual_realizable
#print axioms dram_sense_amp_balanced_rate_formula
#print axioms dram_sense_amp_balanced_residual_realizable
#print axioms dram_sense_amp_full_basin_realizable
#print axioms dram_sense_amp_full_basin_scalar_determinate
#print axioms dram_sense_amp_vector_balanced_on_domain
#print axioms dram_sense_amp_vector_projects_to_scalar_on_domain
#print axioms dram_sense_amp_vector_determinate_on_domain
#print axioms dram_sense_amp_full_basin_no_overshoot
#print axioms dram_sense_amp_full_basin_monotone
#print axioms dram_sense_amp_small_signal_behavior
#print axioms dram_sense_amp_small_signal_scalar_determinate
#print axioms dram_sense_amp_small_signal_realizable
#print axioms dram_sense_amp_small_signal_performance_realizable
#print axioms dram_sense_amp_full_basin_regeneration
