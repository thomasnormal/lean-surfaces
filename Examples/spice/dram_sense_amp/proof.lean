import LeanModels.Spice.DramDifferentialSenseSpec
import LeanModels.Circuit.Surface
import LeanModels.Circuit.Enclosure

namespace Examples.spice.dram_sense_amp.proof

open LeanModels.Circuit LeanModels.Spice

load_circuit dramSenseAmp from
  "Examples/spice/dram_sense_amp/dram_sense_amp.cir"

def dramSenseAmpLayout : DramDifferentialSenseLayout :=
  match dramSenseAmp.toDramDifferentialSense with
  | .ok layout => layout
  | .error _ => default

theorem dram_sense_amp_projection :
    dramSenseAmp.toDramDifferentialSense = .ok dramSenseAmpLayout := by
  circuit_reduce

theorem dram_sense_amp_layout :
    dramSenseAmpLayout =
      { trueLine := ⟨0⟩
        complementLine := ⟨2⟩
        supply := ⟨3⟩
        ground := ⟨1⟩
        truePmos := ⟨2⟩
        trueNmos := ⟨3⟩
        complementPmos := ⟨4⟩
        complementNmos := ⟨5⟩
        trueCapacitor := ⟨0⟩
        complementCapacitor := ⟨1⟩
        nThreshold := 1
        pThreshold := 1
        nBeta := 1 / 10000
        pBeta := 1 / 10000
        trueCapacitance := 3 / 10000000000000
        complementCapacitance := 3 / 10000000000000 } := by
  circuit_reduce

theorem dram_sense_amp_parameters :
    dramSenseAmpLayout.fabricated =
      { nThreshold := 1
        pThreshold := 1
        nBeta := 1 / 10000
        pBeta := 1 / 10000
        trueCapacitance := 3 / 10000000000000
        complementCapacitance := 3 / 10000000000000 } := by
  rw [dram_sense_amp_layout]
  norm_num [DramDifferentialSenseLayout.fabricated]

theorem dram_sense_amp_equation_manifest :
    EquationManifest DramDifferentialSenseProgram [] := by
  constructor
  · simp
  · intro contract hcontract
    rcases hcontract with ⟨clause, hclause⟩
    cases clause <;>
      simp [DramDifferentialSenseProgram] at hclause

noncomputable def dramSenseWorld
    (initialTrue initialComplement horizon : ℝ) :
    DramDifferentialSenseWorld :=
  deterministicWorld dramSenseAmpLayout.fabricated
    { supply := 5
      initialTrue
      initialComplement
      horizon }

theorem dram_sense_amp_rail_admissible (value : Bool) :
    DramDifferentialSenseAdmissible
      (dramSenseWorld
        (if value then 5 else 0)
        (if value then 0 else 5) 1) := by
  cases value <;>
    norm_num [DramDifferentialSenseAdmissible, dramSenseWorld,
      deterministicWorld, dram_sense_amp_parameters]

theorem dram_sense_amp_rail_realizable (value : Bool) :
    ∃ boundary,
      DramDifferentialSenseBehavior
        (dramSenseWorld
          (if value then 5 else 0)
          (if value then 0 else 5) 1)
        boundary () := by
  apply dramDifferentialSense_rail_realizable
    (dram_sense_amp_rail_admissible value) value
  · cases value <;>
      rfl
  · cases value <;>
      rfl

theorem dram_sense_amp_metastable_admissible :
    DramDifferentialSenseAdmissible
      (dramSenseWorld (5 / 2) (5 / 2) 1) := by
  norm_num [DramDifferentialSenseAdmissible, dramSenseWorld,
    deterministicWorld, dram_sense_amp_parameters]

theorem dram_sense_amp_metastable_realizable :
    ∃ boundary,
      DramDifferentialSenseBehavior
        (dramSenseWorld (5 / 2) (5 / 2) 1) boundary () := by
  apply dramDifferentialSense_metastable_realizable
    dram_sense_amp_metastable_admissible
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · rfl
  · rfl

theorem dram_sense_amp_metastable_not_resolved (value : Bool) :
    ¬ DramDifferentialSenseResolved
      (dramSenseWorld (5 / 2) (5 / 2) 1)
      ⟨fun _time =>
        dramDifferentialSenseMetastableState 5⟩ value := by
  apply dramDifferentialSense_metastable_not_resolved
  norm_num [dramSenseWorld, deterministicWorld]

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
    0 < derivative .trueLine - derivative .complementLine := by
  apply dramDifferentialSense_nominal_local_regeneration
    (world := dramSenseWorld (5 / 2 + deviation)
      (5 / 2 - deviation) 1)
    (time := time) (deviation := deviation)
  · rfl
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · exact hdeviation
  · exact hregion
  · exact hresidual

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
    0 < derivative .trueLine - derivative .complementLine := by
  apply dramDifferentialSense_nominal_unbalanced_regeneration
      (world := dramSenseWorld initialTrue initialComplement horizon)
      (time := time) (state := state) (derivative := derivative)
  · rfl
  · simpa [dramSenseWorld, deterministicWorld,
      nominalDramDifferentialSenseInstance] using
      dram_sense_amp_parameters
  · exact hstate
  · exact horder
  · exact hnotRail
  · exact hresidual

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
    derivative .trueLine - derivative .complementLine < 0 := by
  apply dramDifferentialSense_nominal_unbalanced_regeneration_reverse
      (world := dramSenseWorld initialTrue initialComplement horizon)
      (time := time) (state := state) (derivative := derivative)
  · rfl
  · simpa [dramSenseWorld, deterministicWorld,
      nominalDramDifferentialSenseInstance] using
      dram_sense_amp_parameters
  · exact hstate
  · exact horder
  · exact hnotRail
  · exact hresidual

/-- Every instantaneous state of the source-backed latch has a primitive
derivative satisfying both capacitor KCL equations. -/
theorem dram_sense_amp_unbalanced_residual_realizable
    {initialTrue initialComplement horizon time : ℝ}
    {state : VectorState DramDifferentialSenseIndex} :
    ∃ derivative : VectorState DramDifferentialSenseIndex,
      dramDifferentialSenseDAE.residual
        (dramSenseWorld initialTrue initialComplement horizon)
        time state derivative := by
  apply dramDifferentialSense_residual_realizable
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]

theorem dram_sense_amp_balanced_rate_formula
    {deviation : ℝ}
    (hdeviation0 : 0 ≤ deviation)
    (hdeviationRail : deviation ≤ 5 / 2) :
    dramDifferentialSenseBalancedRate
        (dramSenseWorld (5 / 2 + deviation)
          (5 / 2 - deviation) 1)
        deviation =
      dramDifferentialSenseNominalBalancedRate deviation := by
  apply dramDifferentialSense_nominal_balanced_rate_eq
  · rfl
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · exact hdeviation0
  · exact hdeviationRail

theorem dram_sense_amp_balanced_residual_realizable
    {time deviation : ℝ} :
    ∃ derivative : VectorState DramDifferentialSenseIndex,
      dramDifferentialSenseDAE.residual
        (dramSenseWorld (5 / 2 + deviation)
          (5 / 2 - deviation) 1)
        time (dramDifferentialSenseBalancedState 5 deviation)
        derivative := by
  apply dramDifferentialSense_balanced_residual_realizable
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · norm_num [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]

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
          boundary := by
  let world :=
    dramSenseWorld
      (5 / 2 + initialDeviation)
      (5 / 2 - initialDeviation) horizon
  obtain ⟨trajectory, hinitial, hbehavior, hinvariant⟩ :=
    dramDifferentialSense_nominal_behavior_realizable
      (world := world)
      (initialDeviation := initialDeviation)
      (hsupply := rfl)
      (hnThreshold := by
        simp [world, dramSenseWorld, deterministicWorld,
          dram_sense_amp_parameters])
      (hpThreshold := by
        simp [world, dramSenseWorld, deterministicWorld,
          dram_sense_amp_parameters])
      (hnBeta := by
        simp [world, dramSenseWorld, deterministicWorld,
          dram_sense_amp_parameters])
      (hpBeta := by
        simp [world, dramSenseWorld, deterministicWorld,
          dram_sense_amp_parameters])
      (hTrueCap := by
        simp [world, dramSenseWorld, deterministicWorld,
          dram_sense_amp_parameters])
      (hComplementCap := by
        simp [world, dramSenseWorld, deterministicWorld,
          dram_sense_amp_parameters])
      hinitial0 hinitialRail hhorizon rfl rfl
  let boundary :=
    dramDifferentialSenseBalancedBoundary world trajectory
  refine ⟨boundary, hbehavior, ?_⟩
  intro time htime0 htimeHorizon
  have hdeviation :=
    hinvariant time htime0 htimeHorizon
  simp only [boundary,
    dramDifferentialSenseBalancedBoundary,
    dramDifferentialSenseBalancedTrace,
    dramDifferentialSenseBalancedState]
  change
    0 ≤ 5 / 2 + trajectory time ∧
      5 / 2 + trajectory time ≤ 5 ∧
      0 ≤ 5 / 2 - trajectory time ∧
      5 / 2 - trajectory time ≤ 5
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

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
    first time = second time := by
  apply dramDifferentialSense_nominal_scalar_determinate
    (world := dramSenseWorld
      (5 / 2 + initialDeviation)
      (5 / 2 - initialDeviation) horizon)
    (first := first) (second := second)
  · rfl
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · exact hfirst
  · exact hsecond
  · exact hinitial
  · exact htime0
  · exact htimeHorizon

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
        boundary.voltage time .complementLine = 5 := by
  let world :=
    dramSenseWorld
      (5 / 2 + initialDeviation)
      (5 / 2 - initialDeviation) horizon
  have hevolution :
      dramDifferentialSenseDAE.ACBehavesOn world horizon
        boundary.voltage := by
    exact hbehavior .evolution
  have hstateDomain :
      ∀ point, 0 ≤ point → point ≤ horizon →
        DramDifferentialSenseStateInRailDomain world
          (boundary.voltage point) := by
    intro point hpoint0 hpointHorizon
    simpa [DramDifferentialSenseStateInRailDomain,
      DramDifferentialSenseInRailDomain] using
      hdomain point hpoint0 hpointHorizon
  have hinitialTrue :
      boundary.voltage 0 .trueLine = 5 / 2 + initialDeviation := by
    exact hbehavior .initialTrue
  have hinitialComplement :
      boundary.voltage 0 .complementLine =
        5 / 2 - initialDeviation := by
    exact hbehavior .initialComplement
  have hinitial :
      boundary.voltage 0 .trueLine +
          boundary.voltage 0 .complementLine =
        world.environment.supply := by
    simp [world, dramSenseWorld, deterministicWorld,
      hinitialTrue, hinitialComplement]
  have hbalanced :=
    dramDifferentialSense_balanced_invariant_on_domain
      (world := world)
      (trace := boundary.voltage)
      (by simp [world, dramSenseWorld, deterministicWorld,
        dram_sense_amp_parameters])
      (by simp [world, dramSenseWorld, deterministicWorld,
        dram_sense_amp_parameters])
      (by norm_num [world, dramSenseWorld, deterministicWorld,
        dram_sense_amp_parameters])
      (by simp [world, dramSenseWorld, deterministicWorld,
        dram_sense_amp_parameters])
      (by norm_num [world, dramSenseWorld, deterministicWorld,
        dram_sense_amp_parameters])
      hevolution hstateDomain hinitial
  simpa [world, dramSenseWorld, deterministicWorld] using
    hbalanced time htime0 htimeHorizon

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
      (dramDifferentialSenseTraceDeviation boundary.voltage) := by
  let world :=
    dramSenseWorld
      (5 / 2 + initialDeviation)
      (5 / 2 - initialDeviation) horizon
  have hevolution :
      dramDifferentialSenseDAE.ACBehavesOn world horizon
        boundary.voltage :=
    hbehavior .evolution
  have hstateDomain :
      ∀ point, 0 ≤ point → point ≤ horizon →
        DramDifferentialSenseStateInRailDomain world
          (boundary.voltage point) := by
    intro point hpoint0 hpointHorizon
    simpa [DramDifferentialSenseStateInRailDomain,
      DramDifferentialSenseInRailDomain] using
      hdomain point hpoint0 hpointHorizon
  have hinitialTrue :
      boundary.voltage 0 .trueLine = 5 / 2 + initialDeviation :=
    hbehavior .initialTrue
  have hinitialComplement :
      boundary.voltage 0 .complementLine =
        5 / 2 - initialDeviation :=
    hbehavior .initialComplement
  apply dramDifferentialSense_balanced_ac_project_on_domain
    (world := world)
  · simp [world, dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [world, dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · norm_num [world, dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [world, dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · norm_num [world, dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · exact hevolution
  · exact hstateDomain
  · simp [world, dramSenseWorld, deterministicWorld,
      hinitialTrue, hinitialComplement]

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
    first.voltage time = second.voltage time := by
  let world :=
    dramSenseWorld
      (5 / 2 + initialDeviation)
      (5 / 2 - initialDeviation) horizon
  have hinitial : first.voltage 0 = second.voltage 0 := by
    funext index
    cases index
    · have hfirstInitial :
          first.voltage 0 .trueLine =
            5 / 2 + initialDeviation :=
        hfirst .initialTrue
      have hsecondInitial :
          second.voltage 0 .trueLine =
            5 / 2 + initialDeviation :=
        hsecond .initialTrue
      linarith
    · have hfirstInitial :
          first.voltage 0 .complementLine =
            5 / 2 - initialDeviation :=
        hfirst .initialComplement
      have hsecondInitial :
          second.voltage 0 .complementLine =
            5 / 2 - initialDeviation :=
        hsecond .initialComplement
      linarith
  have hinitialBalanced :
      first.voltage 0 .trueLine + first.voltage 0 .complementLine =
        world.environment.supply := by
    have htrue :
        first.voltage 0 .trueLine =
          5 / 2 + initialDeviation :=
      hfirst .initialTrue
    have hcomplement :
        first.voltage 0 .complementLine =
          5 / 2 - initialDeviation :=
      hfirst .initialComplement
    simp [world, dramSenseWorld, deterministicWorld]
    linarith
  apply dramDifferentialSense_nominal_vector_determinate_on_domain
    (world := world)
    (first := first.voltage) (second := second.voltage)
  · rfl
  · simp [world, dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [world, dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [world, dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [world, dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [world, dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [world, dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · exact hfirst .evolution
  · exact hsecond .evolution
  · intro point hpoint0 hpointHorizon
    simpa [DramDifferentialSenseStateInRailDomain,
      DramDifferentialSenseInRailDomain] using
      hfirstDomain point hpoint0 hpointHorizon
  · intro point hpoint0 hpointHorizon
    simpa [DramDifferentialSenseStateInRailDomain,
      DramDifferentialSenseInRailDomain] using
      hsecondDomain point hpoint0 hpointHorizon
  · exact hinitial
  · exact hinitialBalanced
  · exact htime0
  · exact htimeHorizon

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
    NoOvershoot trajectory 0 (5 / 2) horizon := by
  apply dramDifferentialSense_nominal_scalar_invariant
    (world := dramSenseWorld
      (5 / 2 + initialDeviation)
      (5 / 2 - initialDeviation) horizon)
    (trajectory := trajectory)
  · rfl
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · exact hbehavior
  · exact hinitial
  · exact hinitial0
  · exact hinitialRail

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
    MonotoneOn trajectory (Set.Icc (0 : ℝ) horizon) := by
  apply dramDifferentialSense_nominal_scalar_monotone
    (world := dramSenseWorld
      (5 / 2 + initialDeviation)
      (5 / 2 - initialDeviation) horizon)
    (trajectory := trajectory)
  · rfl
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · exact hbehavior
  · exact hinitial
  · exact hinitial0
  · exact hinitialRail

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
        initialDeviation) () := by
  apply dramDifferentialSense_small_signal_behavior
    (world := dramSenseWorld
      (5 / 2 + initialDeviation)
      (5 / 2 - initialDeviation) horizon)
    (initialDeviation := initialDeviation)
  · rfl
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · exact hinitial
  · exact hhorizon
  · exact hsmall
  · rfl
  · rfl

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
        initialDeviation time := by
  apply dramDifferentialSense_small_signal_scalar_eq_trace
    (world := dramSenseWorld
      (5 / 2 + initialDeviation)
      (5 / 2 - initialDeviation) horizon)
    (deviation := deviation)
    (initialDeviation := initialDeviation)
    (horizon := horizon)
  · rfl
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · exact hbehavior
  · exact hinitial
  · exact hdomain
  · exact htime0
  · exact htimeHorizon

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
        boundary () :=
  ⟨dramDifferentialSenseSmallSignalBoundary
      (dramSenseWorld
        (5 / 2 + initialDeviation)
        (5 / 2 - initialDeviation) horizon)
      initialDeviation,
    dram_sense_amp_small_signal_behavior
      hinitial hhorizon hsmall⟩

/-- The small-signal cap at a 100 mV deviation over one nanosecond, certified
by the growth certificate at split depth 10. Shared by all three corollaries
below, which is why it is a named fact rather than three inline proofs. -/
theorem dram_sense_amp_small_signal_cap_1ns :
    dramDifferentialSenseSmallSignalTrace (1 / 10) (1 / 1000000000) ≤
      1 / 2 := by
  unfold dramDifferentialSenseSmallSignalTrace
  have h1 : (1000000000 : ℝ) * (1 / 1000000000) = 1 := by norm_num
  rw [h1]
  have he : Real.exp (1 : ℝ) ≤ (10 / 9) ^ 10 :=
    LeanModels.Circuit.exp_le_of_pow_le 10 (by norm_num) (by norm_num)
      (by norm_num)
  nlinarith [(Real.exp_pos (1:ℝ)).le]

/-- A 250 mV margin is reached within one nanosecond from a 100 mV deviation.
The deadline is a `log`, so this uses the DEADLINE certificate at split depth
8 (`5/2 ≤ (9/8)^8`), not the growth one. -/
theorem dram_sense_amp_small_signal_deadline_1ns :
    dramDifferentialSenseSmallSignalDeadline (1 / 10) (1 / 4) ≤
      1 / 1000000000 := by
  unfold dramDifferentialSenseSmallSignalDeadline
  have hlog : Real.log ((1 / 4 : ℝ) / (1 / 10)) ≤ 1 := by
    have h : ((1 : ℝ) / 4) / (1 / 10) = 5 / 2 := by norm_num
    rw [h]
    exact LeanModels.Circuit.log_le_of_le_pow (by norm_num) (by norm_num) 8
      (by norm_num) (by norm_num)
  exact max_le (by norm_num) (by linarith)

/-- A13/A14 INSTANTIATED.  `dram_sense_amp_small_signal_realizable` carried
`hsmall` -- the bound that keeps the small-signal linearisation honest -- as a
HYPOTHESIS; here it is discharged.

This deck needed the one direction the F2 kit did not have.  Its deviation
GROWS -- a sense amplifier regenerates -- so the honest bound is on growth from
above, while every settling deck needed decay from above. -/
theorem dram_sense_amp_small_signal_realizable_at_1ns :
    ∃ boundary,
      DramDifferentialSenseBehavior
        (dramSenseWorld (5 / 2 + 1 / 10) (5 / 2 - 1 / 10) (1 / 1000000000))
        boundary () :=
  dram_sense_amp_small_signal_realizable (by norm_num) (by norm_num)
    dram_sense_amp_small_signal_cap_1ns

/-- The witnessing boundary itself, not merely its existence. -/
theorem dram_sense_amp_small_signal_behavior_at_1ns :
    DramDifferentialSenseBehavior
      (dramSenseWorld (5 / 2 + 1 / 10) (5 / 2 - 1 / 10) (1 / 1000000000))
      (dramDifferentialSenseSmallSignalBoundary
        (dramSenseWorld (5 / 2 + 1 / 10) (5 / 2 - 1 / 10) (1 / 1000000000))
        (1 / 10)) () :=
  dram_sense_amp_small_signal_behavior (by norm_num) (by norm_num)
    dram_sense_amp_small_signal_cap_1ns

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
            initialDeviation required) := by
  let world :=
    dramSenseWorld
      (5 / 2 + initialDeviation)
      (5 / 2 - initialDeviation) horizon
  let boundary :=
    dramDifferentialSenseSmallSignalBoundary
      world initialDeviation
  have hhorizon : 0 ≤ horizon :=
    le_trans
      (le_max_left 0
        (Real.log (required / initialDeviation) /
          1000000000))
      hdeadline
  refine ⟨boundary, ?_, ?_, ?_⟩
  · exact dram_sense_amp_small_signal_behavior
      hinitial.le hhorizon hsmall
  · apply dramDifferentialSense_small_signal_witness_in_domain
    · rfl
    · exact hinitial.le
    · exact hsmall
  · apply dramDifferentialSense_small_signal_witness_reaches_margin
      hinitial hrequired
    exact hdeadline

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
      derivative .trueLine + derivative .complementLine = 0 := by
  apply dramDifferentialSense_nominal_balanced_regeneration
    (world := dramSenseWorld (5 / 2 + deviation)
      (5 / 2 - deviation) 1)
    (time := time) (deviation := deviation)
    (derivative := derivative)
  · rfl
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · simp [dramSenseWorld, deterministicWorld,
      dram_sense_amp_parameters]
  · exact hdeviation
  · exact hdeviationRail
  · exact hresidual

#equation_guard DramDifferentialSenseProgram forbids
  [DramDifferentialSenseResolved, DramDifferentialSenseInitialMargin]

#equation_report dram_sense_amp_equation_manifest

#print axioms dram_sense_amp_projection
#print axioms dram_sense_amp_parameters
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

/-- A14: the last exp/log certificate in the tier's F2 census.  Both of this
theorem's numeric hypotheses are discharged, so the sense amplifier's
PERFORMANCE claim -- reaching a 250 mV margin, in the rail domain, within one
nanosecond -- holds outright. -/
theorem dram_sense_amp_small_signal_performance_at_1ns :
    ∃ boundary,
      DramDifferentialSenseBehavior
          (dramSenseWorld (5 / 2 + 1 / 10) (5 / 2 - 1 / 10) (1 / 1000000000))
          boundary () ∧
        DramDifferentialSenseInRailDomain
          (dramSenseWorld (5 / 2 + 1 / 10) (5 / 2 - 1 / 10) (1 / 1000000000))
          boundary ∧
        DramDifferentialSenseReachesMargin
          (dramSenseWorld (5 / 2 + 1 / 10) (5 / 2 - 1 / 10) (1 / 1000000000))
          boundary true (1 / 4)
          (dramDifferentialSenseSmallSignalDeadline (1 / 10) (1 / 4)) :=
  dram_sense_amp_small_signal_performance_realizable (by norm_num)
    (by norm_num) dram_sense_amp_small_signal_deadline_1ns
    dram_sense_amp_small_signal_cap_1ns

/-- A15 / F3 GROUNDED.  `dram_sense_amp_vector_determinate_on_domain` says any
two rail-domain trajectories agree.  That is universally quantified over the
domain premises, so it would hold just as well of a deck no trajectory can
satisfy.  A14's performance witness supplies the missing inhabitant, which is
the same two-link chain `2026-08-24-analog-1` established for assurance cases,
arriving now at a determinacy theorem. -/
theorem dram_sense_amp_determinacy_grounded_at_1ns :
    ∃ boundary,
      DramDifferentialSenseBehavior
          (dramSenseWorld (5 / 2 + 1 / 10) (5 / 2 - 1 / 10) (1 / 1000000000)) boundary () ∧
        DramDifferentialSenseInRailDomain
          (dramSenseWorld (5 / 2 + 1 / 10) (5 / 2 - 1 / 10) (1 / 1000000000)) boundary := by
  obtain ⟨boundary, hbehavior, hdomain, -⟩ :=
    dram_sense_amp_small_signal_performance_at_1ns
  exact ⟨boundary, hbehavior, hdomain⟩

/-- A15: determinacy with the horizon instantiated to one nanosecond.  The
domain premises remain, because they are properties of the two trajectories
being COMPARED rather than of the deck -- and the theorem above shows they are
satisfiable. -/
theorem dram_sense_amp_determinate_at_1ns
    {first second : DramDifferentialSenseBoundary}
    (hfirst :
      DramDifferentialSenseBehavior
        (dramSenseWorld (5 / 2 + 1 / 10) (5 / 2 - 1 / 10) (1 / 1000000000)) first ())
    (hsecond :
      DramDifferentialSenseBehavior
        (dramSenseWorld (5 / 2 + 1 / 10) (5 / 2 - 1 / 10) (1 / 1000000000)) second ())
    (hfirstDomain :
      DramDifferentialSenseInRailDomain
        (dramSenseWorld (5 / 2 + 1 / 10) (5 / 2 - 1 / 10) (1 / 1000000000)) first)
    (hsecondDomain :
      DramDifferentialSenseInRailDomain
        (dramSenseWorld (5 / 2 + 1 / 10) (5 / 2 - 1 / 10) (1 / 1000000000)) second)
    {time : ℝ} (htime0 : 0 ≤ time)
    (htimeHorizon : time ≤ 1 / 1000000000) :
    first.voltage time = second.voltage time :=
  dram_sense_amp_vector_determinate_on_domain hfirst hsecond hfirstDomain
    hsecondDomain htime0 htimeHorizon

end Examples.spice.dram_sense_amp.proof
