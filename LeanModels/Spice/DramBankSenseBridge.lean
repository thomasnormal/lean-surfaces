import LeanModels.Spice.DramBankCore
import LeanModels.Spice.DramDifferentialSenseUnbalanced
import LeanModels.Spice.DramSenseCoupling

/-!
# DRAM bank-to-differential-sense phase bridge

This module defines the interface between a source-derived bank
charge-sharing endpoint and a differential latch. Physical line identity is
fixed: the selected bank bitline feeds the latch `trueLine`, and the reference
feeds `complementLine`. A stored zero therefore produces a negative
differential; no proof swaps the lines based on the unknown bit.

The generated 256x32 deck now contains the differential latch and paired
transmission-gate couplers. Its source projector certifies that topology and
the latch parameters. The source-derived finite coupling trajectory proves
`DramDifferentialSenseCouplingReady` after every positive coupling duration.
Full latch convergence and restore remain explicit refinement targets; the
older 2x2 deck still uses its legacy two-inverter path.
-/

namespace LeanModels.Spice

open LeanModels.Circuit

/-- Fixed-identity ideal interface state. A physical finite coupling phase
must refine its actual latch-node state to an ordering compatible with this
target; it is not definitionally identified with the target. -/
noncomputable def dramBankDifferentialSenseInitialState
    (selectedBitline referenceBitline : ℝ) :
    VectorState DramDifferentialSenseIndex
  | .trueLine => selectedBitline
  | .complementLine => referenceBitline

/-- The exact postcondition required from the paired transmission-gate
coupling phase. It records only rail closure, fixed-polarity ordering, and
exclusion of an already-resolved rail endpoint. It does not assert a desired
logic output. -/
def DramDifferentialSenseCouplingReady
    (world : DramDifferentialSenseWorld) (value : Bool)
    (state : VectorState DramDifferentialSenseIndex) : Prop :=
  DramDifferentialSenseStateInRailDomain world state ∧
    if value then
      state .complementLine < state .trueLine ∧
        (state .trueLine < world.environment.supply ∨
          0 < state .complementLine)
    else
      state .trueLine < state .complementLine ∧
        (state .complementLine < world.environment.supply ∨
          0 < state .trueLine)

/-- Projection of the two latch-node coordinates at the end of the physical
transmission-gate coupling phase. -/
noncomputable def dramSenseCouplingLatchState
    (bitline reference time : ℝ) :
    VectorState DramDifferentialSenseIndex
  | .trueLine =>
      nominalDramSenseCouplingPairRight bitline (5 / 2) time
  | .complementLine =>
      nominalDramSenseCouplingPairRight reference (5 / 2) time

/-- Any positive duration of the source-derived passive coupling trajectory
establishes the exact ordering required by the regenerative latch. The
stored-zero case uses the proved strict monotonicity of the unequal-rate MOS1
traces; no ideal connection or equal-rate approximation is assumed. -/
theorem dramSenseCoupling_nominal_establishes_ready
    {world : DramDifferentialSenseWorld}
    {value : Bool}
    {bitline reference time : ℝ}
    (hsupply : world.environment.supply = 5)
    (hbitlineLower : 2 ≤ bitline)
    (hbitlineUpper : bitline ≤ 3)
    (hreferenceLower : 2 ≤ reference)
    (hreferenceUpper : reference ≤ 3)
    (htime : 0 < time)
    (hlogic :
      if value then
        5 / 2 < bitline ∧ reference ≤ 5 / 2
      else
        bitline < reference ∧ reference ≤ 5 / 2) :
    DramDifferentialSenseCouplingReady world value
      (dramSenseCouplingLatchState bitline reference time) := by
  have hbitBounds :=
    nominalDramSenseCouplingPair_bounds
      hbitlineLower hbitlineUpper
      (by norm_num : (2 : ℝ) ≤ 5 / 2)
      (by norm_num : (5 / 2 : ℝ) ≤ 3)
      (le_refl 3) htime.le
  have hrefBounds :=
    nominalDramSenseCouplingPair_bounds
      hreferenceLower hreferenceUpper
      (by norm_num : (2 : ℝ) ≤ 5 / 2)
      (by norm_num : (5 / 2 : ℝ) ≤ 3)
      (le_refl 3) htime.le
  have hdomain :
      DramDifferentialSenseStateInRailDomain world
        (dramSenseCouplingLatchState bitline reference time) := by
    unfold DramDifferentialSenseStateInRailDomain
      dramSenseCouplingLatchState
    rw [hsupply]
    exact
      ⟨by linarith [hbitBounds.2.2.1],
        by linarith [hbitBounds.2.2.2],
        by linarith [hrefBounds.2.2.1],
        by linarith [hrefBounds.2.2.2]⟩
  refine ⟨hdomain, ?_⟩
  cases hvalue : value
  · simp only [hvalue, Bool.false_eq_true, if_false] at hlogic ⊢
    change
      nominalDramSenseCouplingPairRight bitline (5 / 2) time <
          nominalDramSenseCouplingPairRight reference (5 / 2) time ∧
        (nominalDramSenseCouplingPairRight reference (5 / 2) time <
            world.environment.supply ∨
          0 <
            nominalDramSenseCouplingPairRight bitline (5 / 2) time)
    have horder :=
      nominalDramSenseCouplingPairRight_strictMono_below
        hbitlineLower hlogic.1 hlogic.2 htime
    exact
      ⟨horder, Or.inr (by linarith [hbitBounds.2.2.1])⟩
  · simp only [hvalue, if_true] at hlogic ⊢
    change
      nominalDramSenseCouplingPairRight reference (5 / 2) time <
          nominalDramSenseCouplingPairRight bitline (5 / 2) time ∧
        (nominalDramSenseCouplingPairRight bitline (5 / 2) time <
            world.environment.supply ∨
          0 <
            nominalDramSenseCouplingPairRight reference (5 / 2) time)
    have htrueAbove :
        5 / 2 <
          nominalDramSenseCouplingPairRight
            bitline (5 / 2) time :=
      nominalDramSenseCouplingPairRight_gt_initial
        hlogic.1 hbitlineUpper
        (by norm_num : (5 / 2 : ℝ) ≤ 3) htime
    have hcomplementAtMost :
        nominalDramSenseCouplingPairRight
            reference (5 / 2) time ≤ 5 / 2 :=
      nominalDramSenseCouplingPairRight_le_initial
        hlogic.2 hreferenceUpper
        (by norm_num : (5 / 2 : ℝ) ≤ 3) htime.le
    exact
      ⟨by linarith,
        Or.inr (by linarith [hrefBounds.2.2.1])⟩

/-- Once a finite coupling phase establishes `CouplingReady`, the nominal
source-model latch strictly amplifies the signed differential. -/
theorem dramDifferentialSense_nominal_coupling_ready_regeneration
    {world : DramDifferentialSenseWorld}
    {time : ℝ} {value : Bool}
    {state derivative : VectorState DramDifferentialSenseIndex}
    (hsupply : world.environment.supply = 5)
    (hinstance :
      world.fabricated = nominalDramDifferentialSenseInstance)
    (hready : DramDifferentialSenseCouplingReady world value state)
    (hresidual :
      dramDifferentialSenseDAE.residual world time state derivative) :
    if value then
      0 < derivative .trueLine - derivative .complementLine
    else
      derivative .trueLine - derivative .complementLine < 0 := by
  cases hvalue : value
  · simp only [hvalue, Bool.false_eq_true, if_false] at hready ⊢
    have hnotRail := hready.2.2
    rw [hsupply] at hnotRail
    exact
      dramDifferentialSense_nominal_unbalanced_regeneration_reverse
        hsupply hinstance hready.1 hready.2.1 hnotRail hresidual
  · simp only [hvalue, if_true] at hready ⊢
    have hnotRail := hready.2.2
    rw [hsupply] at hnotRail
    exact
      dramDifferentialSense_nominal_unbalanced_regeneration
        hsupply hinstance hready.1 hready.2.1 hnotRail hresidual

/-- A source-derived coupling endpoint can be used as the actual initial
condition of a non-vacuous finite-horizon latch behavior. The returned domain
invariant is proved from the primitive clamped-extension barrier argument; it
is not an assumption inside `CouplingReady`. -/
theorem dramDifferentialSense_nominal_coupling_ready_realizable
    {world : DramDifferentialSenseWorld}
    {value : Bool}
    {state : VectorState DramDifferentialSenseIndex}
    (hsupply : world.environment.supply = 5)
    (hinstance :
      world.fabricated = nominalDramDifferentialSenseInstance)
    (hhorizon : 0 ≤ world.environment.horizon)
    (hready :
      DramDifferentialSenseCouplingReady world value state)
    (hinitialTrue :
      world.environment.initialTrue = state .trueLine)
    (hinitialComplement :
      world.environment.initialComplement =
        state .complementLine) :
    ∃ boundary : DramDifferentialSenseBoundary,
      DramDifferentialSenseBehavior world boundary () ∧
      ∀ time ∈ Set.Icc (0 : ℝ) world.environment.horizon,
        boundary.voltage time .trueLine ∈ Set.Icc (0 : ℝ) 5 ∧
          boundary.voltage time .complementLine ∈
            Set.Icc (0 : ℝ) 5 := by
  apply dramDifferentialSense_nominal_unbalanced_realizable
    hsupply hinstance hhorizon
  · rw [hinitialTrue]
    have hdomain := hready.1
    unfold DramDifferentialSenseStateInRailDomain at hdomain
    rw [hsupply] at hdomain
    exact ⟨hdomain.1, hdomain.2.1⟩
  · rw [hinitialComplement]
    have hdomain := hready.1
    unfold DramDifferentialSenseStateInRailDomain at hdomain
    rw [hsupply] at hdomain
    exact ⟨hdomain.2.2.1, hdomain.2.2.2⟩

/-- A `CouplingReady` state has an inhabited smooth nominal latch trajectory
whose correctly signed differential never decreases. The clamped proof field
is accompanied at every time by the exact primitive MOS1/capacitor-KCL
residual, justified by the returned rail-domain invariant. -/
theorem
    dramDifferentialSense_nominal_coupling_ready_margin_realizable
    {world : DramDifferentialSenseWorld}
    {value : Bool}
    {state : VectorState DramDifferentialSenseIndex}
    (hsupply : world.environment.supply = 5)
    (hinstance :
      world.fabricated = nominalDramDifferentialSenseInstance)
    (hhorizon : 0 ≤ world.environment.horizon)
    (hready :
      DramDifferentialSenseCouplingReady world value state) :
    ∃ trajectory : ℝ → DramDifferentialSensePair,
      trajectory 0 = dramDifferentialSenseStatePair state ∧
      (∀ time ∈ Set.Icc (0 : ℝ) world.environment.horizon,
        HasDerivWithinAt trajectory
          (dramDifferentialSenseNominalClampedPairRate
            (trajectory time))
          (Set.Icc (0 : ℝ) world.environment.horizon) time) ∧
      (∀ time ∈ Set.Icc (0 : ℝ) world.environment.horizon,
        (trajectory time).1 ∈ Set.Icc (0 : ℝ) 5 ∧
          (trajectory time).2 ∈ Set.Icc (0 : ℝ) 5) ∧
      MonotoneOn
        (fun time =>
          dramDifferentialSenseSignedPairMargin value
            (trajectory time))
        (Set.Icc (0 : ℝ) world.environment.horizon) ∧
      ∀ time ∈ Set.Icc (0 : ℝ) world.environment.horizon,
        dramDifferentialSenseDAE.residual world time
          (dramDifferentialSensePairState (trajectory time))
          (dramDifferentialSensePairState
            (dramDifferentialSenseNominalClampedPairRate
              (trajectory time))) := by
  have hdomain := hready.1
  unfold DramDifferentialSenseStateInRailDomain at hdomain
  rw [hsupply] at hdomain
  have hinitialTrue :
      (dramDifferentialSenseStatePair state).1 ∈
        Set.Icc (0 : ℝ) 5 :=
    ⟨hdomain.1, hdomain.2.1⟩
  have hinitialComplement :
      (dramDifferentialSenseStatePair state).2 ∈
        Set.Icc (0 : ℝ) 5 :=
    ⟨hdomain.2.2.1, hdomain.2.2.2⟩
  have hinitialOrder :
      if value then
        (dramDifferentialSenseStatePair state).2 <
          (dramDifferentialSenseStatePair state).1
      else
        (dramDifferentialSenseStatePair state).1 <
          (dramDifferentialSenseStatePair state).2 := by
    cases hvalue : value
    · simp only [hvalue, Bool.false_eq_true, if_false] at hready ⊢
      exact hready.2.1
    · simp only [hvalue, if_true] at hready ⊢
      exact hready.2.1
  obtain ⟨trajectory, hinitial, hsolution, hinvariant,
      hmonotone⟩ :=
    dramDifferentialSenseNominalClampedPairRate_realizable_signed_monotone
      value (dramDifferentialSenseStatePair state)
      hhorizon hinitialTrue hinitialComplement hinitialOrder
  refine
    ⟨trajectory, hinitial, hsolution, hinvariant, hmonotone, ?_⟩
  intro time htime
  have hpointDomain := hinvariant time htime
  exact
    dramDifferentialSenseNominalClampedPairRate_residual
      hsupply hinstance
      ⟨hpointDomain.1.1, hpointDomain.1.2,
        hpointDomain.2.1, hpointDomain.2.2⟩

/-- A finite source-derived coupling endpoint has a non-vacuous nominal
resolution witness for every requested signed margin between the delivered
margin and full rail separation. -/
theorem
    dramDifferentialSense_nominal_coupling_ready_resolution_realizable
    {world : DramDifferentialSenseWorld}
    {value : Bool}
    {state : VectorState DramDifferentialSenseIndex}
    (required : ℝ)
    (hsupply : world.environment.supply = 5)
    (hinstance :
      world.fabricated = nominalDramDifferentialSenseInstance)
    (hhorizon : 0 ≤ world.environment.horizon)
    (hready :
      DramDifferentialSenseCouplingReady world value state)
    (hrequiredLower :
      dramDifferentialSenseSignedPairMargin value
          (dramDifferentialSenseStatePair state) ≤ required)
    (hrequiredUpper : required < 5) :
    Nonempty
      (DramDifferentialSenseResolutionWitness world value
        (dramDifferentialSenseStatePair state) required) := by
  have hdomain := hready.1
  unfold DramDifferentialSenseStateInRailDomain at hdomain
  rw [hsupply] at hdomain
  have hinitialTrue :
      (dramDifferentialSenseStatePair state).1 ∈
        Set.Icc (0 : ℝ) 5 :=
    ⟨hdomain.1, hdomain.2.1⟩
  have hinitialComplement :
      (dramDifferentialSenseStatePair state).2 ∈
        Set.Icc (0 : ℝ) 5 :=
    ⟨hdomain.2.2.1, hdomain.2.2.2⟩
  have hinitialOrder :
      if value then
        (dramDifferentialSenseStatePair state).2 <
          (dramDifferentialSenseStatePair state).1
      else
        (dramDifferentialSenseStatePair state).1 <
          (dramDifferentialSenseStatePair state).2 := by
    cases hvalue : value
    · simp only [hvalue, Bool.false_eq_true, if_false] at hready ⊢
      exact hready.2.1
    · simp only [hvalue, if_true] at hready ⊢
      exact hready.2.1
  exact
    dramDifferentialSense_nominal_resolution_realizable
      value (dramDifferentialSenseStatePair state) required
      hsupply hinstance hhorizon
      hinitialTrue hinitialComplement hinitialOrder
      hrequiredLower hrequiredUpper

/-- Source-derived precharge and charge sharing put the candidate
differential-sense input inside the rail rectangle and deliver at least
`3/22 V` signed margin for either stored bit. -/
theorem DramBankCoreReadBehavior.differential_sense_initial
    {profile : DramBankCoreProfile rows columns}
    {bankWorld : DramBankCoreReadWorld rows columns}
    {observation : DramBankCoreReadObservation rows columns}
    {senseWorld : DramDifferentialSenseWorld}
    (hprofile : DramBankCoreNominalProfile profile)
    (hbehavior :
      DramBankCoreReadBehavior profile bankWorld observation ())
    (hsupply : senseWorld.environment.supply = 5)
    (column : Fin columns) :
    DramDifferentialSenseStateInRailDomain senseWorld
        (dramBankDifferentialSenseInitialState
          (observation.activated.bitline column)
          (observation.prechargedBitline column)) ∧
      if bankWorld.bits.bits bankWorld.row column then
        3 / 22 ≤
          dramBankDifferentialSenseInitialState
              (observation.activated.bitline column)
              (observation.prechargedBitline column) .trueLine -
            dramBankDifferentialSenseInitialState
              (observation.activated.bitline column)
              (observation.prechargedBitline column) .complementLine
      else
        3 / 22 ≤
          dramBankDifferentialSenseInitialState
              (observation.activated.bitline column)
              (observation.prechargedBitline column) .complementLine -
            dramBankDifferentialSenseInitialState
              (observation.activated.bitline column)
              (observation.prechargedBitline column) .trueLine := by
  have hprecharge :=
    hbehavior.precharged_voltage_bounds hprofile column
  have hactivated := hbehavior.activated_voltage hprofile column
  have hmargin :=
    hbehavior.activated_reference_margin hprofile column
  have hactivatedRail :
      0 ≤ observation.activated.bitline column ∧
        observation.activated.bitline column ≤ 5 := by
    cases hbit : bankWorld.bits.bits bankWorld.row column
    · simp only [hbit, Bool.false_eq_true, if_false] at hactivated
      constructor <;> linarith [hactivated.1, hactivated.2]
    · simp only [hbit, if_true] at hactivated
      constructor <;> linarith [hactivated.1, hactivated.2]
  constructor
  · change
      0 ≤ observation.activated.bitline column ∧
        observation.activated.bitline column ≤
          senseWorld.environment.supply ∧
        0 ≤ observation.prechargedBitline column ∧
        observation.prechargedBitline column ≤
          senseWorld.environment.supply
    rw [hsupply]
    exact
      ⟨hactivatedRail.1, hactivatedRail.2,
        by linarith [hprecharge.1], by linarith [hprecharge.2]⟩
  · cases hbit : bankWorld.bits.bits bankWorld.row column
    · simp only [hbit, Bool.false_eq_true, if_false] at hmargin ⊢
      dsimp [dramBankDifferentialSenseInitialState]
      linarith
    · simp only [hbit, if_true] at hmargin ⊢
      dsimp [dramBankDifferentialSenseInitialState]
      linarith

/-- The nominal four-MOS/two-capacitor latch initially amplifies the signed
margin delivered by the bank phase: positive for a stored one and negative
for a stored zero. This is a local DAE result, not yet a finite-horizon
connection or resolution-time theorem. -/
theorem DramBankCoreReadBehavior.differential_sense_local_regeneration
    {profile : DramBankCoreProfile rows columns}
    {bankWorld : DramBankCoreReadWorld rows columns}
    {observation : DramBankCoreReadObservation rows columns}
    {senseWorld : DramDifferentialSenseWorld}
    {time : ℝ}
    {derivative : VectorState DramDifferentialSenseIndex}
    (hprofile : DramBankCoreNominalProfile profile)
    (hbehavior :
      DramBankCoreReadBehavior profile bankWorld observation ())
    (hsupply : senseWorld.environment.supply = 5)
    (hinstance :
      senseWorld.fabricated = nominalDramDifferentialSenseInstance)
    (column : Fin columns)
    (hresidual :
      dramDifferentialSenseDAE.residual senseWorld time
        (dramBankDifferentialSenseInitialState
          (observation.activated.bitline column)
          (observation.prechargedBitline column))
        derivative) :
    if bankWorld.bits.bits bankWorld.row column then
      0 < derivative .trueLine - derivative .complementLine
    else
      derivative .trueLine - derivative .complementLine < 0 := by
  have hinitial :=
    hbehavior.differential_sense_initial
      hprofile hsupply column
  have hprecharge :=
    hbehavior.precharged_voltage_bounds hprofile column
  cases hbit : bankWorld.bits.bits bankWorld.row column
  · simp only [hbit, Bool.false_eq_true, if_false] at hinitial ⊢
    apply dramDifferentialSense_nominal_unbalanced_regeneration_reverse
      hsupply hinstance hinitial.1
    · change
        observation.activated.bitline column <
          observation.prechargedBitline column
      dsimp [dramBankDifferentialSenseInitialState] at hinitial
      nlinarith [hinitial.2]
    · left
      dsimp [dramBankDifferentialSenseInitialState]
      linarith [hprecharge.2]
    · exact hresidual
  · simp only [hbit, if_true] at hinitial ⊢
    apply dramDifferentialSense_nominal_unbalanced_regeneration
      hsupply hinstance hinitial.1
    · change
        observation.prechargedBitline column <
          observation.activated.bitline column
      dsimp [dramBankDifferentialSenseInitialState] at hinitial
      nlinarith [hinitial.2]
    · right
      dsimp [dramBankDifferentialSenseInitialState]
      linarith [hprecharge.1]
    · exact hresidual

/-- Positive latch capacitances inhabit the bridge's primitive residual at
the supplied bank state. -/
theorem dramBankDifferentialSense_initial_residual_realizable
    {senseWorld : DramDifferentialSenseWorld}
    {time selectedBitline referenceBitline : ℝ}
    (hTrueCapacitance : 0 < senseWorld.fabricated.trueCapacitance)
    (hComplementCapacitance :
      0 < senseWorld.fabricated.complementCapacitance) :
    ∃ derivative : VectorState DramDifferentialSenseIndex,
      dramDifferentialSenseDAE.residual senseWorld time
        (dramBankDifferentialSenseInitialState
          selectedBitline referenceBitline)
        derivative :=
  dramDifferentialSense_residual_realizable
    hTrueCapacitance hComplementCapacitance

end LeanModels.Spice
