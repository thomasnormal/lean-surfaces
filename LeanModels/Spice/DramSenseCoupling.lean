import LeanModels.Spice.Mos1
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import LeanModels.Circuit.Equation
import LeanModels.Circuit.Transient
import LeanModels.Circuit.World

/-!
# DRAM bitline-to-sense-latch coupling phase

This module models the finite phase in which two enabled CMOS transmission
gates connect the selected bitline and reference bitline to the two
precharged sense-latch nodes. The latch supplies are not energized during
this phase. The semantic root contains only the four capacitor KCL equations
and the source/drain-symmetric MOS1 terminal currents of the two transmission
gates.

The desired sense decision is deliberately absent. The first theorem layer
proves residual realizability, pairwise charge conservation, and the strict
initial derivative ordering delivered by a bitline/reference voltage margin.
-/

namespace LeanModels.Spice

open LeanModels.Circuit Set MeasureTheory

inductive DramSenseCouplingIndex
  | bitline
  | reference
  | trueLine
  | complementLine
deriving Repr, DecidableEq, BEq, Inhabited

structure DramSenseCouplingInstance where
  nThreshold : ℝ
  nBeta : ℝ
  pThreshold : ℝ
  pBeta : ℝ
  bitlineCapacitance : ℝ
  referenceCapacitance : ℝ
  trueCapacitance : ℝ
  complementCapacitance : ℝ

structure DramSenseCouplingEnvironment where
  supply : ℝ
  initialBitline : ℝ
  initialReference : ℝ
  initialTrue : ℝ
  initialComplement : ℝ
  horizon : ℝ

abbrev DramSenseCouplingWorld :=
  RunWorld DramSenseCouplingInstance
    DramSenseCouplingEnvironment Unit Unit

structure DramSenseCouplingBoundary where
  voltage : VectorTrace DramSenseCouplingIndex

def DramSenseCouplingAdmissible
    (world : DramSenseCouplingWorld) : Prop :=
  0 < world.fabricated.nThreshold ∧
  0 < world.fabricated.nBeta ∧
  0 < world.fabricated.pThreshold ∧
  0 < world.fabricated.pBeta ∧
  0 < world.fabricated.bitlineCapacitance ∧
  0 < world.fabricated.referenceCapacitance ∧
  0 < world.fabricated.trueCapacitance ∧
  0 < world.fabricated.complementCapacitance ∧
  0 ≤ world.environment.horizon

noncomputable def DramSenseCouplingInstance.nmosParams
    (device : DramSenseCouplingInstance) : Mos1Params :=
  { polarity := .nmos
    threshold := device.nThreshold
    beta := device.nBeta
    lambda := 0 }

noncomputable def DramSenseCouplingInstance.pmosParams
    (device : DramSenseCouplingInstance) : Mos1Params :=
  { polarity := .pmos
    threshold := device.pThreshold
    beta := device.pBeta
    lambda := 0 }

/-- Conventional current leaving `left` through an enabled CMOS
transmission gate and entering `right`. -/
noncomputable def dramSenseCouplingCurrent
    (device : DramSenseCouplingInstance)
    (supply left right : ℝ) : ℝ :=
  mos1TerminalCurrent device.nmosParams supply left right +
    mos1TerminalCurrent device.pmosParams 0 left right

/-- Four capacitor KCL equations for the two independent coupling pairs. -/
noncomputable def dramSenseCouplingDAE :
    VectorDAE DramSenseCouplingWorld DramSenseCouplingIndex where
  residual world _time state derivative :=
    let bitCurrent :=
      dramSenseCouplingCurrent world.fabricated
        world.environment.supply
        (state .bitline) (state .trueLine)
    let referenceCurrent :=
      dramSenseCouplingCurrent world.fabricated
        world.environment.supply
        (state .reference) (state .complementLine)
    world.fabricated.bitlineCapacitance * derivative .bitline +
          bitCurrent = 0 ∧
      world.fabricated.trueCapacitance * derivative .trueLine -
          bitCurrent = 0 ∧
      world.fabricated.referenceCapacitance * derivative .reference +
          referenceCurrent = 0 ∧
      world.fabricated.complementCapacitance *
            derivative .complementLine -
          referenceCurrent = 0

inductive DramSenseCouplingClause where
  | initialBitline
  | initialReference
  | initialTrue
  | initialComplement
  | evolution
deriving Repr, DecidableEq

noncomputable def DramSenseCouplingProgram :
    EquationProgram DramSenseCouplingClause DramSenseCouplingWorld
      DramSenseCouplingBoundary Unit where
  origin
    | .initialBitline =>
        .initialCondition "selected bitline capacitor voltage"
    | .initialReference =>
        .initialCondition "reference bitline capacitor voltage"
    | .initialTrue =>
        .initialCondition "precharged true latch-node voltage"
    | .initialComplement =>
        .initialCondition "precharged complement latch-node voltage"
    | .evolution =>
        .evolution "paired transmission-gate/capacitor KCL vector DAE"
  equation clause world boundary _internal :=
    match clause with
    | .initialBitline =>
        boundary.voltage 0 .bitline =
          world.environment.initialBitline
    | .initialReference =>
        boundary.voltage 0 .reference =
          world.environment.initialReference
    | .initialTrue =>
        boundary.voltage 0 .trueLine =
          world.environment.initialTrue
    | .initialComplement =>
        boundary.voltage 0 .complementLine =
          world.environment.initialComplement
    | .evolution =>
        dramSenseCouplingDAE.ACBehavesOn world
          world.environment.horizon boundary.voltage

noncomputable def DramSenseCouplingBehavior :
    Behavior DramSenseCouplingWorld DramSenseCouplingBoundary Unit :=
  DramSenseCouplingProgram.behavior

theorem dramSenseCouplingProgram_physicsOnly :
    DramSenseCouplingProgram.PhysicsOnly := by
  unfold EquationProgram.PhysicsOnly
  intro clause
  cases clause <;> rfl

theorem dramSenseCouplingEquationManifest :
    EquationManifest DramSenseCouplingProgram [] := by
  constructor
  · simp
  · intro contract hcontract
    rcases hcontract with ⟨clause, hclause⟩
    cases clause <;> simp [DramSenseCouplingProgram] at hclause

/-- Positive capacitor values make the primitive residual inhabited at every
state. This is the pointwise non-vacuity companion for later direction
theorems. -/
theorem dramSenseCoupling_residual_realizable
    {world : DramSenseCouplingWorld}
    {time : ℝ}
    {state : VectorState DramSenseCouplingIndex}
    (hBitlineCapacitance :
      0 < world.fabricated.bitlineCapacitance)
    (hReferenceCapacitance :
      0 < world.fabricated.referenceCapacitance)
    (hTrueCapacitance :
      0 < world.fabricated.trueCapacitance)
    (hComplementCapacitance :
      0 < world.fabricated.complementCapacitance) :
    ∃ derivative : VectorState DramSenseCouplingIndex,
      dramSenseCouplingDAE.residual world time state derivative := by
  let bitCurrent :=
    dramSenseCouplingCurrent world.fabricated
      world.environment.supply
      (state .bitline) (state .trueLine)
  let referenceCurrent :=
    dramSenseCouplingCurrent world.fabricated
      world.environment.supply
      (state .reference) (state .complementLine)
  let derivative : VectorState DramSenseCouplingIndex
    | .bitline =>
        -bitCurrent / world.fabricated.bitlineCapacitance
    | .reference =>
        -referenceCurrent / world.fabricated.referenceCapacitance
    | .trueLine =>
        bitCurrent / world.fabricated.trueCapacitance
    | .complementLine =>
        referenceCurrent /
          world.fabricated.complementCapacitance
  refine ⟨derivative, ?_⟩
  change
    world.fabricated.bitlineCapacitance *
          (-bitCurrent / world.fabricated.bitlineCapacitance) +
          bitCurrent = 0 ∧
      world.fabricated.trueCapacitance *
          (bitCurrent / world.fabricated.trueCapacitance) -
          bitCurrent = 0 ∧
      world.fabricated.referenceCapacitance *
          (-referenceCurrent /
            world.fabricated.referenceCapacitance) +
          referenceCurrent = 0 ∧
      world.fabricated.complementCapacitance *
          (referenceCurrent /
            world.fabricated.complementCapacitance) -
          referenceCurrent = 0
  field_simp <;> simp

/-- Each coupling pair conserves capacitor charge because its internal
transmission-gate current appears with opposite KCL signs. -/
theorem dramSenseCoupling_residual_conserves_pair_charge
    {world : DramSenseCouplingWorld}
    {time : ℝ}
    {state derivative : VectorState DramSenseCouplingIndex}
    (hresidual :
      dramSenseCouplingDAE.residual world time state derivative) :
    world.fabricated.bitlineCapacitance * derivative .bitline +
          world.fabricated.trueCapacitance * derivative .trueLine = 0 ∧
      world.fabricated.referenceCapacitance * derivative .reference +
          world.fabricated.complementCapacitance *
            derivative .complementLine = 0 := by
  change
    world.fabricated.bitlineCapacitance * derivative .bitline +
          dramSenseCouplingCurrent world.fabricated
            world.environment.supply
            (state .bitline) (state .trueLine) = 0 ∧
      world.fabricated.trueCapacitance * derivative .trueLine -
          dramSenseCouplingCurrent world.fabricated
            world.environment.supply
            (state .bitline) (state .trueLine) = 0 ∧
      world.fabricated.referenceCapacitance * derivative .reference +
          dramSenseCouplingCurrent world.fabricated
            world.environment.supply
            (state .reference) (state .complementLine) = 0 ∧
      world.fabricated.complementCapacitance *
            derivative .complementLine -
          dramSenseCouplingCurrent world.fabricated
            world.environment.supply
            (state .reference) (state .complementLine) = 0 at hresidual
  constructor
  · linarith [hresidual.1, hresidual.2.1]
  · linarith [hresidual.2.2.1, hresidual.2.2.2]

noncomputable def dramSenseCouplingBitPairCharge
    (device : DramSenseCouplingInstance)
    (state : VectorState DramSenseCouplingIndex) : ℝ :=
  device.bitlineCapacitance * state .bitline +
    device.trueCapacitance * state .trueLine

noncomputable def dramSenseCouplingReferencePairCharge
    (device : DramSenseCouplingInstance)
    (state : VectorState DramSenseCouplingIndex) : ℝ :=
  device.referenceCapacitance * state .reference +
    device.complementCapacitance * state .complementLine

/-- Every physical coupling trajectory conserves charge separately on the
selected-data pair and the reference pair. This is a trajectory theorem from
the four primitive capacitor KCL equations, not an endpoint premise. -/
theorem dramSenseCoupling_behavior_conserves_pair_charge
    {world : DramSenseCouplingWorld}
    {boundary : DramSenseCouplingBoundary}
    (hbehavior : DramSenseCouplingBehavior world boundary ()) :
    ∀ time ∈ Icc 0 world.environment.horizon,
      dramSenseCouplingBitPairCharge world.fabricated
          (boundary.voltage time) =
          dramSenseCouplingBitPairCharge world.fabricated
            (boundary.voltage 0) ∧
        dramSenseCouplingReferencePairCharge world.fabricated
          (boundary.voltage time) =
          dramSenseCouplingReferencePairCharge world.fabricated
            (boundary.voltage 0) := by
  intro target htarget
  have hdae := hbehavior .evolution
  have hdae' :
      ∀ᵐ time,
        time ∈ uIcc 0 world.environment.horizon →
          ∃ derivative : VectorState DramSenseCouplingIndex,
            (∀ index,
              HasDerivAt (fun t => boundary.voltage t index)
                (derivative index) time) ∧
            dramSenseCouplingDAE.residual world time
              (boundary.voltage time) derivative :=
    (ae_restrict_iff' measurableSet_uIcc).mp hdae.2.2
  have htarget' :
      target ∈ uIcc 0 world.environment.horizon := by
    simpa [uIcc_of_le hdae.1] using htarget
  have hzero' :
      (0 : ℝ) ∈ uIcc 0 world.environment.horizon := by
    simp [uIcc_of_le hdae.1, hdae.1]
  constructor
  · let charge : ℝ → ℝ :=
      (fun time =>
        world.fabricated.bitlineCapacitance *
          boundary.voltage time .bitline) +
      (fun time =>
        world.fabricated.trueCapacitance *
          boundary.voltage time .trueLine)
    have hac : AbsolutelyContinuousOnInterval charge 0
        world.environment.horizon := by
      exact
        ((hdae.2.1 .bitline).const_mul
          world.fabricated.bitlineCapacitance).add
        ((hdae.2.1 .trueLine).const_mul
          world.fabricated.trueCapacitance)
    have hzero :
        ∀ᵐ time,
          time ∈ uIcc 0 world.environment.horizon →
            HasDerivAt charge 0 time := by
      filter_upwards [hdae'] with time htime hmem
      obtain ⟨derivative, hderivative, hresidual⟩ := htime hmem
      have hcharge :
          HasDerivAt charge
            (world.fabricated.bitlineCapacitance *
                derivative .bitline +
              world.fabricated.trueCapacitance *
                derivative .trueLine)
            time := by
        exact
          ((hderivative .bitline).const_mul
            world.fabricated.bitlineCapacitance).add
          ((hderivative .trueLine).const_mul
            world.fabricated.trueCapacitance)
      rw [(dramSenseCoupling_residual_conserves_pair_charge
        hresidual).1] at hcharge
      exact hcharge
    obtain ⟨constant, hconstant⟩ :=
      hac.const_of_ae_hasDerivAt_zero hzero
    change charge target = charge 0
    exact
      (hconstant target htarget').trans
        (hconstant 0 hzero').symm
  · let charge : ℝ → ℝ :=
      (fun time =>
        world.fabricated.referenceCapacitance *
          boundary.voltage time .reference) +
      (fun time =>
        world.fabricated.complementCapacitance *
          boundary.voltage time .complementLine)
    have hac : AbsolutelyContinuousOnInterval charge 0
        world.environment.horizon := by
      exact
        ((hdae.2.1 .reference).const_mul
          world.fabricated.referenceCapacitance).add
        ((hdae.2.1 .complementLine).const_mul
          world.fabricated.complementCapacitance)
    have hzero :
        ∀ᵐ time,
          time ∈ uIcc 0 world.environment.horizon →
            HasDerivAt charge 0 time := by
      filter_upwards [hdae'] with time htime hmem
      obtain ⟨derivative, hderivative, hresidual⟩ := htime hmem
      have hcharge :
          HasDerivAt charge
            (world.fabricated.referenceCapacitance *
                derivative .reference +
              world.fabricated.complementCapacitance *
                derivative .complementLine)
            time := by
        exact
          ((hderivative .reference).const_mul
            world.fabricated.referenceCapacitance).add
          ((hderivative .complementLine).const_mul
            world.fabricated.complementCapacitance)
      rw [(dramSenseCoupling_residual_conserves_pair_charge
        hresidual).2] at hcharge
      exact hcharge
    obtain ⟨constant, hconstant⟩ :=
      hac.const_of_ae_hasDerivAt_zero hzero
    change charge target = charge 0
    exact
      (hconstant target htarget').trans
        (hconstant 0 hzero').symm

/-- The exact transmission-gate and capacitor parameters used by the
generated 256x32 bank. -/
noncomputable def nominalDramSenseCouplingInstance :
    DramSenseCouplingInstance :=
  { nThreshold := 1
    nBeta := 1 / 10000
    pThreshold := 1
    pBeta := 1 / 20000
    bitlineCapacitance := 3 / 10000000000000
    referenceCapacitance := 3 / 10000000000000
    trueCapacitance := 3 / 10000000000000
    complementCapacitance := 3 / 10000000000000 }

noncomputable def dramSenseCouplingInitialState
    (bitline reference : ℝ) :
    VectorState DramSenseCouplingIndex
  | .bitline => bitline
  | .reference => reference
  | .trueLine => 5 / 2
  | .complementLine => 5 / 2

/-- On the complete bank coupling domain, the two exact bidirectional MOS1
currents of the transmission gate simplify to a positive conductance times
terminal voltage difference. The conductance depends only on the conserved
common-mode sum. -/
theorem nominalDramSenseCouplingCurrent_eq_linear
    {left right : ℝ}
    (hleftLower : 2 ≤ left)
    (hleftUpper : left ≤ 3)
    (hrightLower : 2 ≤ right)
    (hrightUpper : right ≤ 3) :
    dramSenseCouplingCurrent nominalDramSenseCouplingInstance
        5 left right =
      (14 - (left + right)) / 40000 * (left - right) := by
  unfold dramSenseCouplingCurrent
    nominalDramSenseCouplingInstance
    DramSenseCouplingInstance.nmosParams
    DramSenseCouplingInstance.pmosParams
    mos1TerminalCurrent mos1ForwardCurrent
  norm_num
  split_ifs <;> nlinarith

noncomputable def nominalDramSenseCouplingRate
    (left right : ℝ) : ℝ :=
  (14 - (left + right)) * 500000000 / 3

noncomputable def nominalDramSenseCouplingDecay
    (left right time : ℝ) : ℝ :=
  Real.exp (-nominalDramSenseCouplingRate left right * time)

noncomputable def nominalDramSenseCouplingPairLeft
    (left right : ℝ) : DenseTrace ℝ :=
  fun time =>
    (left + right +
      (left - right) *
        nominalDramSenseCouplingDecay left right time) / 2

noncomputable def nominalDramSenseCouplingPairRight
    (left right : ℝ) : DenseTrace ℝ :=
  fun time =>
    (left + right -
      (left - right) *
        nominalDramSenseCouplingDecay left right time) / 2

theorem nominalDramSenseCouplingRate_pos
    {left right : ℝ}
    (hleftUpper : left ≤ 3)
    (hrightUpper : right ≤ 3) :
    0 < nominalDramSenseCouplingRate left right := by
  unfold nominalDramSenseCouplingRate
  norm_num
  linarith

theorem nominalDramSenseCouplingDecay_pos
    (left right time : ℝ) :
    0 < nominalDramSenseCouplingDecay left right time :=
  Real.exp_pos _

theorem nominalDramSenseCouplingDecay_le_one
    {left right time : ℝ}
    (hleftUpper : left ≤ 3)
    (hrightUpper : right ≤ 3)
    (htime : 0 ≤ time) :
    nominalDramSenseCouplingDecay left right time ≤ 1 := by
  unfold nominalDramSenseCouplingDecay
  rw [Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr
      (nominalDramSenseCouplingRate_pos hleftUpper hrightUpper).le)
    htime

theorem nominalDramSenseCouplingPair_initial
    (left right : ℝ) :
    nominalDramSenseCouplingPairLeft left right 0 = left ∧
      nominalDramSenseCouplingPairRight left right 0 = right := by
  simp [nominalDramSenseCouplingPairLeft,
    nominalDramSenseCouplingPairRight,
    nominalDramSenseCouplingDecay]

/-- Both capacitor voltages stay in the convex hull of their initial
voltages; the coupling phase therefore has no overshoot. -/
theorem nominalDramSenseCouplingPair_bounds
    {left right lower upper time : ℝ}
    (hleftLower : lower ≤ left)
    (hleftUpper : left ≤ upper)
    (hrightLower : lower ≤ right)
    (hrightUpper : right ≤ upper)
    (hupperRail : upper ≤ 3)
    (htime : 0 ≤ time) :
    lower ≤ nominalDramSenseCouplingPairLeft left right time ∧
      nominalDramSenseCouplingPairLeft left right time ≤ upper ∧
      lower ≤ nominalDramSenseCouplingPairRight left right time ∧
      nominalDramSenseCouplingPairRight left right time ≤ upper := by
  let weight := nominalDramSenseCouplingDecay left right time
  have hweight0 : 0 ≤ weight :=
    (nominalDramSenseCouplingDecay_pos left right time).le
  have hweight1 : weight ≤ 1 :=
    nominalDramSenseCouplingDecay_le_one
      (hleftUpper.trans hupperRail)
      (hrightUpper.trans hupperRail) htime
  have hleftFormula :
      nominalDramSenseCouplingPairLeft left right time =
        ((1 + weight) * left + (1 - weight) * right) / 2 := by
    dsimp [weight]
    unfold nominalDramSenseCouplingPairLeft
    ring
  have hrightFormula :
      nominalDramSenseCouplingPairRight left right time =
        ((1 - weight) * left + (1 + weight) * right) / 2 := by
    dsimp [weight]
    unfold nominalDramSenseCouplingPairRight
    ring
  rw [hleftFormula, hrightFormula]
  have hleftLowerWeighted :
      0 ≤ (1 + weight) * (left - lower) :=
    mul_nonneg (by linarith) (by linarith)
  have hrightLowerWeighted :
      0 ≤ (1 - weight) * (right - lower) :=
    mul_nonneg (by linarith) (by linarith)
  have hleftUpperWeighted :
      0 ≤ (1 + weight) * (upper - left) :=
    mul_nonneg (by linarith) (by linarith)
  have hrightUpperWeighted :
      0 ≤ (1 - weight) * (upper - right) :=
    mul_nonneg (by linarith) (by linarith)
  have hleftLowerWeighted' :
      0 ≤ (1 - weight) * (left - lower) :=
    mul_nonneg (by linarith) (by linarith)
  have hrightLowerWeighted' :
      0 ≤ (1 + weight) * (right - lower) :=
    mul_nonneg (by linarith) (by linarith)
  have hleftUpperWeighted' :
      0 ≤ (1 - weight) * (upper - left) :=
    mul_nonneg (by linarith) (by linarith)
  have hrightUpperWeighted' :
      0 ≤ (1 + weight) * (upper - right) :=
    mul_nonneg (by linarith) (by linarith)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem nominalDramSenseCouplingPairLeft_hasDerivAt
    (left right time : ℝ) :
    HasDerivAt
      (nominalDramSenseCouplingPairLeft left right)
      (-nominalDramSenseCouplingRate left right / 2 *
        (left - right) *
        nominalDramSenseCouplingDecay left right time) time := by
  let rate := nominalDramSenseCouplingRate left right
  have hinner :
      HasDerivAt (fun t : ℝ => -rate * t) (-rate) time := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id time).const_mul (-rate)
  have hexponential :
      HasDerivAt (fun t : ℝ => Real.exp (-rate * t))
        (Real.exp (-rate * time) * (-rate)) time :=
    (Real.hasDerivAt_exp (-rate * time)).comp time hinner
  have hscaled := hexponential.const_mul (left - right)
  have hshifted := hscaled.const_add (left + right)
  have hhalved := hshifted.div_const 2
  dsimp only [rate] at hhalved
  change
    HasDerivAt
      (fun t =>
        (left + right +
          (left - right) *
            Real.exp
              (-nominalDramSenseCouplingRate left right * t)) / 2)
      (-nominalDramSenseCouplingRate left right / 2 *
        (left - right) *
        Real.exp
          (-nominalDramSenseCouplingRate left right * time))
      time
  exact hhalved.congr_deriv (by ring)

theorem nominalDramSenseCouplingPairRight_hasDerivAt
    (left right time : ℝ) :
    HasDerivAt
      (nominalDramSenseCouplingPairRight left right)
      (nominalDramSenseCouplingRate left right / 2 *
        (left - right) *
        nominalDramSenseCouplingDecay left right time) time := by
  let rate := nominalDramSenseCouplingRate left right
  have hinner :
      HasDerivAt (fun t : ℝ => -rate * t) (-rate) time := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id time).const_mul (-rate)
  have hexponential :
      HasDerivAt (fun t : ℝ => Real.exp (-rate * t))
        (Real.exp (-rate * time) * (-rate)) time :=
    (Real.hasDerivAt_exp (-rate * time)).comp time hinner
  have hscaled := hexponential.const_mul (-(left - right))
  have hshifted := hscaled.const_add (left + right)
  have hhalved := hshifted.div_const 2
  dsimp only [rate] at hhalved
  change
    HasDerivAt
      (fun t =>
        (left + right -
          (left - right) *
            Real.exp
              (-nominalDramSenseCouplingRate left right * t)) / 2)
      (nominalDramSenseCouplingRate left right / 2 *
        (left - right) *
        Real.exp
          (-nominalDramSenseCouplingRate left right * time))
      time
  have hfunction :
      HasDerivAt
        (fun t =>
          (left + right -
            (left - right) *
              Real.exp
                (-nominalDramSenseCouplingRate left right * t)) / 2)
        (-(left - right) *
            (Real.exp
              (-nominalDramSenseCouplingRate left right * time) *
              -nominalDramSenseCouplingRate left right) / 2)
        time :=
    hhalved.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by ring)
  exact hfunction.congr_deriv (by ring)

theorem nominalDramSenseCouplingPair_absolutelyContinuous
    (left right horizon : ℝ) :
    AbsolutelyContinuousOnInterval
        (nominalDramSenseCouplingPairLeft left right) 0 horizon ∧
      AbsolutelyContinuousOnInterval
        (nominalDramSenseCouplingPairRight left right) 0 horizon := by
  constructor
  · apply ContDiffOn.absolutelyContinuousOnInterval
    unfold nominalDramSenseCouplingPairLeft
      nominalDramSenseCouplingDecay
    fun_prop
  · apply ContDiffOn.absolutelyContinuousOnInterval
    unfold nominalDramSenseCouplingPairRight
      nominalDramSenseCouplingDecay
    fun_prop

theorem nominalDramSenseCouplingDecay_lt_one
    {left right time : ℝ}
    (hleftUpper : left ≤ 3)
    (hrightUpper : right ≤ 3)
    (htime : 0 < time) :
    nominalDramSenseCouplingDecay left right time < 1 := by
  unfold nominalDramSenseCouplingDecay
  rw [Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos
    (neg_lt_zero.mpr
      (nominalDramSenseCouplingRate_pos hleftUpper hrightUpper))
    htime

theorem nominalDramSenseCouplingPairRight_eq
    (left right time : ℝ) :
    nominalDramSenseCouplingPairRight left right time =
      right + (left - right) *
        (1 - nominalDramSenseCouplingDecay left right time) / 2 := by
  unfold nominalDramSenseCouplingPairRight
  ring

theorem nominalDramSenseCouplingPairRight_gt_initial
    {left right time : ℝ}
    (hleft : right < left)
    (hleftUpper : left ≤ 3)
    (hrightUpper : right ≤ 3)
    (htime : 0 < time) :
    right <
      nominalDramSenseCouplingPairRight left right time := by
  rw [nominalDramSenseCouplingPairRight_eq]
  have hweight :
      0 < 1 - nominalDramSenseCouplingDecay left right time := by
    linarith [nominalDramSenseCouplingDecay_lt_one
      hleftUpper hrightUpper htime]
  have hproduct :
      0 < (left - right) *
        (1 - nominalDramSenseCouplingDecay left right time) :=
    mul_pos (by linarith) hweight
  linarith

theorem nominalDramSenseCouplingPairRight_le_initial
    {left right time : ℝ}
    (hleft : left ≤ right)
    (hleftUpper : left ≤ 3)
    (hrightUpper : right ≤ 3)
    (htime : 0 ≤ time) :
    nominalDramSenseCouplingPairRight left right time ≤ right := by
  rw [nominalDramSenseCouplingPairRight_eq]
  have hweight :
      0 ≤ 1 - nominalDramSenseCouplingDecay left right time := by
    linarith [nominalDramSenseCouplingDecay_le_one
      hleftUpper hrightUpper htime]
  have hproduct :
      (left - right) *
          (1 - nominalDramSenseCouplingDecay left right time) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hweight
  linarith

/-- Below the precharge point, a larger bitline voltage produces a strictly
larger coupled latch-node voltage at every positive time. This includes the
different source-derived decay rates; no equal-rate approximation is used. -/
theorem nominalDramSenseCouplingPairRight_strictMono_below
    {left right time : ℝ}
    (hleftLower : 2 ≤ left)
    (horder : left < right)
    (hrightUpper : right ≤ 5 / 2)
    (htime : 0 < time) :
    nominalDramSenseCouplingPairRight left (5 / 2) time <
      nominalDramSenseCouplingPairRight right (5 / 2) time := by
  have hleftUpper : left ≤ 3 := by linarith
  have hrightUpper : right ≤ 3 := by linarith
  have hrate :
      nominalDramSenseCouplingRate right (5 / 2) <
        nominalDramSenseCouplingRate left (5 / 2) := by
    unfold nominalDramSenseCouplingRate
    norm_num
    linarith
  have hdecay :
      nominalDramSenseCouplingDecay left (5 / 2) time <
        nominalDramSenseCouplingDecay right (5 / 2) time := by
    unfold nominalDramSenseCouplingDecay
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hleftWeight :
      0 < 1 -
        nominalDramSenseCouplingDecay left (5 / 2) time := by
    linarith [nominalDramSenseCouplingDecay_lt_one
      hleftUpper (by norm_num : (5 / 2 : ℝ) ≤ 3) htime]
  have hrightWeight :
      0 < 1 -
        nominalDramSenseCouplingDecay right (5 / 2) time := by
    linarith [nominalDramSenseCouplingDecay_lt_one
      hrightUpper (by norm_num : (5 / 2 : ℝ) ≤ 3) htime]
  have hgap :
      5 / 2 - right < 5 / 2 - left := by
    linarith
  have hweight :
      1 - nominalDramSenseCouplingDecay right (5 / 2) time <
        1 - nominalDramSenseCouplingDecay left (5 / 2) time := by
    linarith
  have hproduct₁ :
      (5 / 2 - right) *
          (1 - nominalDramSenseCouplingDecay right (5 / 2) time) <
        (5 / 2 - left) *
          (1 - nominalDramSenseCouplingDecay right (5 / 2) time) :=
    mul_lt_mul_of_pos_right hgap hrightWeight
  have hgapPositive : 0 < 5 / 2 - left := by
    linarith
  have hproduct₂ :
      (5 / 2 - left) *
          (1 - nominalDramSenseCouplingDecay right (5 / 2) time) <
        (5 / 2 - left) *
          (1 - nominalDramSenseCouplingDecay left (5 / 2) time) :=
    mul_lt_mul_of_pos_left hweight hgapPositive
  rw [nominalDramSenseCouplingPairRight_eq,
    nominalDramSenseCouplingPairRight_eq]
  nlinarith

theorem nominalDramSenseCouplingPair_sum
    (left right time : ℝ) :
    nominalDramSenseCouplingPairLeft left right time +
        nominalDramSenseCouplingPairRight left right time =
      left + right := by
  unfold nominalDramSenseCouplingPairLeft
    nominalDramSenseCouplingPairRight
  ring

theorem nominalDramSenseCouplingPair_difference
    (left right time : ℝ) :
    nominalDramSenseCouplingPairLeft left right time -
        nominalDramSenseCouplingPairRight left right time =
      (left - right) *
        nominalDramSenseCouplingDecay left right time := by
  unfold nominalDramSenseCouplingPairLeft
    nominalDramSenseCouplingPairRight
  ring

noncomputable def nominalDramSenseCouplingTrace
    (bitline reference : ℝ) :
    VectorTrace DramSenseCouplingIndex :=
  fun time index =>
    match index with
    | .bitline =>
        nominalDramSenseCouplingPairLeft bitline (5 / 2) time
    | .reference =>
        nominalDramSenseCouplingPairLeft reference (5 / 2) time
    | .trueLine =>
        nominalDramSenseCouplingPairRight bitline (5 / 2) time
    | .complementLine =>
        nominalDramSenseCouplingPairRight reference (5 / 2) time

noncomputable def nominalDramSenseCouplingDerivative
    (bitline reference time : ℝ) :
    VectorState DramSenseCouplingIndex
  | .bitline =>
      -nominalDramSenseCouplingRate bitline (5 / 2) / 2 *
        (bitline - 5 / 2) *
        nominalDramSenseCouplingDecay bitline (5 / 2) time
  | .reference =>
      -nominalDramSenseCouplingRate reference (5 / 2) / 2 *
        (reference - 5 / 2) *
        nominalDramSenseCouplingDecay reference (5 / 2) time
  | .trueLine =>
      nominalDramSenseCouplingRate bitline (5 / 2) / 2 *
        (bitline - 5 / 2) *
        nominalDramSenseCouplingDecay bitline (5 / 2) time
  | .complementLine =>
      nominalDramSenseCouplingRate reference (5 / 2) / 2 *
        (reference - 5 / 2) *
        nominalDramSenseCouplingDecay reference (5 / 2) time

noncomputable def nominalDramSenseCouplingBoundary
    (bitline reference : ℝ) : DramSenseCouplingBoundary :=
  ⟨nominalDramSenseCouplingTrace bitline reference⟩

theorem nominalDramSenseCouplingTrace_initial
    (bitline reference : ℝ) :
    nominalDramSenseCouplingTrace bitline reference 0 =
      dramSenseCouplingInitialState bitline reference := by
  funext index
  cases index <;>
    simp only [nominalDramSenseCouplingTrace,
      dramSenseCouplingInitialState]
  · exact (nominalDramSenseCouplingPair_initial _ _).1
  · exact (nominalDramSenseCouplingPair_initial _ _).1
  · exact (nominalDramSenseCouplingPair_initial _ _).2
  · exact (nominalDramSenseCouplingPair_initial _ _).2

theorem nominalDramSenseCouplingTrace_bounds
    {bitline reference time : ℝ}
    (hbitlineLower : 2 ≤ bitline)
    (hbitlineUpper : bitline ≤ 3)
    (hreferenceLower : 2 ≤ reference)
    (hreferenceUpper : reference ≤ 3)
    (htime : 0 ≤ time) :
    ∀ index,
      2 ≤ nominalDramSenseCouplingTrace bitline reference time index ∧
        nominalDramSenseCouplingTrace bitline reference time index ≤ 3 := by
  have hbit :=
    nominalDramSenseCouplingPair_bounds
      hbitlineLower hbitlineUpper
      (by norm_num : (2 : ℝ) ≤ 5 / 2)
      (by norm_num : (5 / 2 : ℝ) ≤ 3)
      (le_refl 3) htime
  have href :=
    nominalDramSenseCouplingPair_bounds
      hreferenceLower hreferenceUpper
      (by norm_num : (2 : ℝ) ≤ 5 / 2)
      (by norm_num : (5 / 2 : ℝ) ≤ 3)
      (le_refl 3) htime
  intro index
  cases index
  · exact ⟨hbit.1, hbit.2.1⟩
  · exact ⟨href.1, href.2.1⟩
  · exact ⟨hbit.2.2.1, hbit.2.2.2⟩
  · exact ⟨href.2.2.1, href.2.2.2⟩

theorem nominalDramSenseCouplingTrace_hasDerivAt
    (bitline reference time : ℝ) :
    ∀ index,
      HasDerivAt
        (fun t =>
          nominalDramSenseCouplingTrace bitline reference t index)
        (nominalDramSenseCouplingDerivative
          bitline reference time index)
        time := by
  intro index
  cases index
  · exact nominalDramSenseCouplingPairLeft_hasDerivAt
      bitline (5 / 2) time
  · exact nominalDramSenseCouplingPairLeft_hasDerivAt
      reference (5 / 2) time
  · exact nominalDramSenseCouplingPairRight_hasDerivAt
      bitline (5 / 2) time
  · exact nominalDramSenseCouplingPairRight_hasDerivAt
      reference (5 / 2) time

theorem nominalDramSenseCouplingTrace_absolutelyContinuous
    (bitline reference horizon : ℝ) :
    ∀ index,
      AbsolutelyContinuousOnInterval
        (fun time =>
          nominalDramSenseCouplingTrace bitline reference time index)
        0 horizon := by
  intro index
  cases index
  · exact
      (nominalDramSenseCouplingPair_absolutelyContinuous
        bitline (5 / 2) horizon).1
  · exact
      (nominalDramSenseCouplingPair_absolutelyContinuous
        reference (5 / 2) horizon).1
  · exact
      (nominalDramSenseCouplingPair_absolutelyContinuous
        bitline (5 / 2) horizon).2
  · exact
      (nominalDramSenseCouplingPair_absolutelyContinuous
        reference (5 / 2) horizon).2

/-- The exponential pair trace satisfies both primitive capacitor KCL
equations pointwise. -/
theorem nominalDramSenseCouplingPair_residual
    {left right time : ℝ}
    (hleftLower : 2 ≤ left)
    (hleftUpper : left ≤ 3)
    (hrightLower : 2 ≤ right)
    (hrightUpper : right ≤ 3)
    (htime : 0 ≤ time) :
    (3 / 10000000000000 : ℝ) *
          (-nominalDramSenseCouplingRate left right / 2 *
            (left - right) *
            nominalDramSenseCouplingDecay left right time) +
        dramSenseCouplingCurrent nominalDramSenseCouplingInstance 5
          (nominalDramSenseCouplingPairLeft left right time)
          (nominalDramSenseCouplingPairRight left right time) = 0 ∧
      (3 / 10000000000000 : ℝ) *
          (nominalDramSenseCouplingRate left right / 2 *
            (left - right) *
            nominalDramSenseCouplingDecay left right time) -
        dramSenseCouplingCurrent nominalDramSenseCouplingInstance 5
          (nominalDramSenseCouplingPairLeft left right time)
          (nominalDramSenseCouplingPairRight left right time) = 0 := by
  have hbounds :=
    nominalDramSenseCouplingPair_bounds
      hleftLower hleftUpper hrightLower hrightUpper
      (le_refl 3) htime
  rw [nominalDramSenseCouplingCurrent_eq_linear
      hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2,
    nominalDramSenseCouplingPair_sum,
    nominalDramSenseCouplingPair_difference]
  unfold nominalDramSenseCouplingRate
  constructor <;> ring

theorem nominalDramSenseCouplingTrace_residual
    {world : DramSenseCouplingWorld}
    {bitline reference time : ℝ}
    (hinstance :
      world.fabricated = nominalDramSenseCouplingInstance)
    (hsupply : world.environment.supply = 5)
    (hbitlineLower : 2 ≤ bitline)
    (hbitlineUpper : bitline ≤ 3)
    (hreferenceLower : 2 ≤ reference)
    (hreferenceUpper : reference ≤ 3)
    (htime : 0 ≤ time) :
    dramSenseCouplingDAE.residual world time
      (nominalDramSenseCouplingTrace bitline reference time)
      (nominalDramSenseCouplingDerivative
        bitline reference time) := by
  have hbit :=
    nominalDramSenseCouplingPair_residual
      hbitlineLower hbitlineUpper
      (by norm_num : (2 : ℝ) ≤ 5 / 2)
      (by norm_num : (5 / 2 : ℝ) ≤ 3) htime
  have href :=
    nominalDramSenseCouplingPair_residual
      hreferenceLower hreferenceUpper
      (by norm_num : (2 : ℝ) ≤ 5 / 2)
      (by norm_num : (5 / 2 : ℝ) ≤ 3) htime
  change
    world.fabricated.bitlineCapacitance *
          (-nominalDramSenseCouplingRate bitline (5 / 2) / 2 *
            (bitline - 5 / 2) *
            nominalDramSenseCouplingDecay bitline (5 / 2) time) +
          dramSenseCouplingCurrent world.fabricated
            world.environment.supply
            (nominalDramSenseCouplingPairLeft bitline (5 / 2) time)
            (nominalDramSenseCouplingPairRight bitline (5 / 2) time) =
        0 ∧
      world.fabricated.trueCapacitance *
          (nominalDramSenseCouplingRate bitline (5 / 2) / 2 *
            (bitline - 5 / 2) *
            nominalDramSenseCouplingDecay bitline (5 / 2) time) -
          dramSenseCouplingCurrent world.fabricated
            world.environment.supply
            (nominalDramSenseCouplingPairLeft bitline (5 / 2) time)
            (nominalDramSenseCouplingPairRight bitline (5 / 2) time) =
        0 ∧
      world.fabricated.referenceCapacitance *
          (-nominalDramSenseCouplingRate reference (5 / 2) / 2 *
            (reference - 5 / 2) *
            nominalDramSenseCouplingDecay reference (5 / 2) time) +
          dramSenseCouplingCurrent world.fabricated
            world.environment.supply
            (nominalDramSenseCouplingPairLeft reference (5 / 2) time)
            (nominalDramSenseCouplingPairRight reference (5 / 2) time) =
        0 ∧
      world.fabricated.complementCapacitance *
          (nominalDramSenseCouplingRate reference (5 / 2) / 2 *
            (reference - 5 / 2) *
            nominalDramSenseCouplingDecay reference (5 / 2) time) -
          dramSenseCouplingCurrent world.fabricated
            world.environment.supply
            (nominalDramSenseCouplingPairLeft reference (5 / 2) time)
            (nominalDramSenseCouplingPairRight reference (5 / 2) time) =
        0
  rw [hinstance, hsupply]
  change
    (3 / 10000000000000 : ℝ) *
          (-nominalDramSenseCouplingRate bitline (5 / 2) / 2 *
            (bitline - 5 / 2) *
            nominalDramSenseCouplingDecay bitline (5 / 2) time) +
          dramSenseCouplingCurrent nominalDramSenseCouplingInstance 5
            (nominalDramSenseCouplingPairLeft bitline (5 / 2) time)
            (nominalDramSenseCouplingPairRight bitline (5 / 2) time) =
        0 ∧
      (3 / 10000000000000 : ℝ) *
          (nominalDramSenseCouplingRate bitline (5 / 2) / 2 *
            (bitline - 5 / 2) *
            nominalDramSenseCouplingDecay bitline (5 / 2) time) -
          dramSenseCouplingCurrent nominalDramSenseCouplingInstance 5
            (nominalDramSenseCouplingPairLeft bitline (5 / 2) time)
            (nominalDramSenseCouplingPairRight bitline (5 / 2) time) =
        0 ∧
      (3 / 10000000000000 : ℝ) *
          (-nominalDramSenseCouplingRate reference (5 / 2) / 2 *
            (reference - 5 / 2) *
            nominalDramSenseCouplingDecay reference (5 / 2) time) +
          dramSenseCouplingCurrent nominalDramSenseCouplingInstance 5
            (nominalDramSenseCouplingPairLeft reference (5 / 2) time)
            (nominalDramSenseCouplingPairRight reference (5 / 2) time) =
        0 ∧
      (3 / 10000000000000 : ℝ) *
          (nominalDramSenseCouplingRate reference (5 / 2) / 2 *
            (reference - 5 / 2) *
            nominalDramSenseCouplingDecay reference (5 / 2) time) -
          dramSenseCouplingCurrent nominalDramSenseCouplingInstance 5
            (nominalDramSenseCouplingPairLeft reference (5 / 2) time)
            (nominalDramSenseCouplingPairRight reference (5 / 2) time) =
        0
  exact ⟨hbit.1, hbit.2, href.1, href.2⟩

/-- The explicit nominal trace is a smooth solution of the source-derived
four-node coupling DAE for every finite nonnegative horizon. -/
theorem nominalDramSenseCouplingTrace_smooth
    {world : DramSenseCouplingWorld}
    {bitline reference horizon : ℝ}
    (hinstance :
      world.fabricated = nominalDramSenseCouplingInstance)
    (hsupply : world.environment.supply = 5)
    (hbitlineLower : 2 ≤ bitline)
    (hbitlineUpper : bitline ≤ 3)
    (hreferenceLower : 2 ≤ reference)
    (hreferenceUpper : reference ≤ 3)
    (hhorizon : 0 ≤ horizon) :
    dramSenseCouplingDAE.SmoothBehavesOn world horizon
      (nominalDramSenseCouplingTrace bitline reference) := by
  refine ⟨hhorizon, ?_⟩
  intro time htime _htimeHorizon
  refine
    ⟨nominalDramSenseCouplingDerivative bitline reference time,
      nominalDramSenseCouplingTrace_hasDerivAt bitline reference time,
      ?_⟩
  exact nominalDramSenseCouplingTrace_residual
    hinstance hsupply hbitlineLower hbitlineUpper
    hreferenceLower hreferenceUpper htime

/-- The smooth witness refines to the absolutely-continuous physical
transient semantics. -/
theorem nominalDramSenseCouplingTrace_ac
    {world : DramSenseCouplingWorld}
    {bitline reference horizon : ℝ}
    (hinstance :
      world.fabricated = nominalDramSenseCouplingInstance)
    (hsupply : world.environment.supply = 5)
    (hbitlineLower : 2 ≤ bitline)
    (hbitlineUpper : bitline ≤ 3)
    (hreferenceLower : 2 ≤ reference)
    (hreferenceUpper : reference ≤ 3)
    (hhorizon : 0 ≤ horizon) :
    dramSenseCouplingDAE.ACBehavesOn world horizon
      (nominalDramSenseCouplingTrace bitline reference) :=
  VectorDAE.acBehavesOn_of_smooth
    (nominalDramSenseCouplingTrace_absolutelyContinuous
      bitline reference horizon)
    (nominalDramSenseCouplingTrace_smooth
      hinstance hsupply hbitlineLower hbitlineUpper
      hreferenceLower hreferenceUpper hhorizon)

def DramSenseCouplingNominalAllowed
    (world : DramSenseCouplingWorld) : Prop :=
  world.fabricated = nominalDramSenseCouplingInstance ∧
  world.environment.supply = 5 ∧
  2 ≤ world.environment.initialBitline ∧
  world.environment.initialBitline ≤ 3 ∧
  2 ≤ world.environment.initialReference ∧
  world.environment.initialReference ≤ 3 ∧
  world.environment.initialTrue = 5 / 2 ∧
  world.environment.initialComplement = 5 / 2 ∧
  0 ≤ world.environment.horizon

theorem dramSenseCouplingNominalAllowed_admissible
    {world : DramSenseCouplingWorld}
    (hallowed : DramSenseCouplingNominalAllowed world) :
    DramSenseCouplingAdmissible world := by
  rcases hallowed with
    ⟨hinstance, _hsupply, _hbitlineLower, _hbitlineUpper,
      _hreferenceLower, _hreferenceUpper, _htrue,
      _hcomplement, hhorizon⟩
  unfold DramSenseCouplingAdmissible
  rw [hinstance]
  norm_num [nominalDramSenseCouplingInstance]
  exact hhorizon

/-- The named exponential trace satisfies the complete equation program.
Initial conditions come from the run environment and evolution comes only
from the source-derived DAE. -/
theorem nominalDramSenseCoupling_behavior
    {world : DramSenseCouplingWorld}
    (hallowed : DramSenseCouplingNominalAllowed world) :
    DramSenseCouplingBehavior world
      (nominalDramSenseCouplingBoundary
        world.environment.initialBitline
        world.environment.initialReference) () := by
  rcases hallowed with
    ⟨hinstance, hsupply, hbitlineLower, hbitlineUpper,
      hreferenceLower, hreferenceUpper, htrue,
      hcomplement, hhorizon⟩
  intro clause
  cases clause
  · change
      nominalDramSenseCouplingPairLeft
          world.environment.initialBitline (5 / 2) 0 =
        world.environment.initialBitline
    exact
      (nominalDramSenseCouplingPair_initial
        world.environment.initialBitline (5 / 2)).1
  · change
      nominalDramSenseCouplingPairLeft
          world.environment.initialReference (5 / 2) 0 =
        world.environment.initialReference
    exact
      (nominalDramSenseCouplingPair_initial
        world.environment.initialReference (5 / 2)).1
  · change
      nominalDramSenseCouplingPairRight
          world.environment.initialBitline (5 / 2) 0 =
        world.environment.initialTrue
    exact
      (nominalDramSenseCouplingPair_initial
        world.environment.initialBitline (5 / 2)).2.trans htrue.symm
  · change
      nominalDramSenseCouplingPairRight
          world.environment.initialReference (5 / 2) 0 =
        world.environment.initialComplement
    exact
      (nominalDramSenseCouplingPair_initial
        world.environment.initialReference (5 / 2)).2.trans
        hcomplement.symm
  · change
      dramSenseCouplingDAE.ACBehavesOn world
        world.environment.horizon
        (nominalDramSenseCouplingTrace
          world.environment.initialBitline
          world.environment.initialReference)
    exact nominalDramSenseCouplingTrace_ac
      hinstance hsupply hbitlineLower hbitlineUpper
      hreferenceLower hreferenceUpper hhorizon

/-- The finite-horizon physical coupling behavior is inhabited for every
nominal allowed environment. -/
theorem dramSenseCoupling_nominal_realizable :
    RealizableUnder DramSenseCouplingBehavior
      DramSenseCouplingNominalAllowed := by
  intro world hallowed
  exact
    ⟨nominalDramSenseCouplingBoundary
        world.environment.initialBitline
        world.environment.initialReference,
      (), nominalDramSenseCoupling_behavior hallowed⟩

/-- The constructed finite-horizon witness remains inside the exact MOS1
domain on which its current identity was proved. -/
theorem nominalDramSenseCoupling_behavior_stays_in_domain
    {world : DramSenseCouplingWorld}
    (hallowed : DramSenseCouplingNominalAllowed world) :
    ∀ time ∈ Set.Icc 0 world.environment.horizon,
      ∀ index,
        2 ≤
            (nominalDramSenseCouplingBoundary
              world.environment.initialBitline
              world.environment.initialReference).voltage time index ∧
          (nominalDramSenseCouplingBoundary
              world.environment.initialBitline
              world.environment.initialReference).voltage time index ≤ 3 := by
  rcases hallowed with
    ⟨_hinstance, _hsupply, hbitlineLower, hbitlineUpper,
      hreferenceLower, hreferenceUpper, _htrue,
      _hcomplement, _hhorizon⟩
  intro time htime index
  exact nominalDramSenseCouplingTrace_bounds
    hbitlineLower hbitlineUpper
    hreferenceLower hreferenceUpper htime.1 index

private theorem nominalDramSenseCouplingCurrent_eq_below
    {voltage : ℝ}
    (hlower : 2 ≤ voltage)
    (hupper : voltage ≤ 5 / 2) :
    dramSenseCouplingCurrent nominalDramSenseCouplingInstance
        5 voltage (5 / 2) =
      -(9 / 40000 * (5 / 2 - voltage) +
        1 / 40000 * (5 / 2 - voltage) ^ 2) := by
  rcases hupper.eq_or_lt with hequal | hlt
  · subst voltage
    norm_num [dramSenseCouplingCurrent,
      nominalDramSenseCouplingInstance,
      DramSenseCouplingInstance.nmosParams,
      DramSenseCouplingInstance.pmosParams,
      mos1TerminalCurrent, mos1ForwardCurrent]
  · unfold dramSenseCouplingCurrent
      nominalDramSenseCouplingInstance
      DramSenseCouplingInstance.nmosParams
      DramSenseCouplingInstance.pmosParams
      mos1TerminalCurrent mos1ForwardCurrent
    norm_num
    split_ifs <;> nlinarith

private theorem nominalDramSenseCouplingCurrent_eq_above
    {voltage : ℝ}
    (hlower : 5 / 2 ≤ voltage)
    (hupper : voltage ≤ 3) :
    dramSenseCouplingCurrent nominalDramSenseCouplingInstance
        5 voltage (5 / 2) =
      9 / 40000 * (voltage - 5 / 2) -
        1 / 40000 * (voltage - 5 / 2) ^ 2 := by
  rcases hlower.eq_or_lt with hequal | hlt
  · subst voltage
    norm_num [dramSenseCouplingCurrent,
      nominalDramSenseCouplingInstance,
      DramSenseCouplingInstance.nmosParams,
      DramSenseCouplingInstance.pmosParams,
      mos1TerminalCurrent, mos1ForwardCurrent]
  · unfold dramSenseCouplingCurrent
      nominalDramSenseCouplingInstance
      DramSenseCouplingInstance.nmosParams
      DramSenseCouplingInstance.pmosParams
      mos1TerminalCurrent mos1ForwardCurrent
    norm_num
    split_ifs <;> nlinarith

/-- In the bank's operating interval below the precharge point, the exact
nominal transmission-gate current is a strictly increasing function of its
bitline terminal voltage. -/
theorem nominalDramSenseCouplingCurrent_strictMono_below
    {left right : ℝ}
    (hleftLower : 2 ≤ left)
    (hleftUpper : left ≤ 5 / 2)
    (hrightUpper : right ≤ 5 / 2)
    (horder : left < right) :
    dramSenseCouplingCurrent nominalDramSenseCouplingInstance
        5 left (5 / 2) <
      dramSenseCouplingCurrent nominalDramSenseCouplingInstance
        5 right (5 / 2) := by
  rw [nominalDramSenseCouplingCurrent_eq_below
      hleftLower hleftUpper,
    nominalDramSenseCouplingCurrent_eq_below
      (by linarith) hrightUpper]
  nlinarith [sq_nonneg (right - left)]

/-- Symmetric monotonicity result above the precharge point. -/
theorem nominalDramSenseCouplingCurrent_strictMono_above
    {left right : ℝ}
    (hleftLower : 5 / 2 ≤ left)
    (hrightUpper : right ≤ 3)
    (horder : left < right) :
    dramSenseCouplingCurrent nominalDramSenseCouplingInstance
        5 left (5 / 2) <
      dramSenseCouplingCurrent nominalDramSenseCouplingInstance
        5 right (5 / 2) := by
  rw [nominalDramSenseCouplingCurrent_eq_above
      hleftLower (by linarith),
    nominalDramSenseCouplingCurrent_eq_above
      (by linarith) hrightUpper]
  nlinarith [sq_nonneg (right - left)]

/-- Strict monotonicity across the complete source-derived bitline interval.
The proof expands the MOS1 cutoff/triode/saturation branches; no ideal-switch
law is assumed. -/
theorem nominalDramSenseCouplingCurrent_strictMono
    {left right : ℝ}
    (hleftLower : 2 ≤ left)
    (hrightUpper : right ≤ 3)
    (horder : left < right) :
    dramSenseCouplingCurrent nominalDramSenseCouplingInstance
        5 left (5 / 2) <
      dramSenseCouplingCurrent nominalDramSenseCouplingInstance
        5 right (5 / 2) := by
  by_cases hleft : left ≤ 5 / 2
  · by_cases hright : right ≤ 5 / 2
    · exact nominalDramSenseCouplingCurrent_strictMono_below
        hleftLower hleft hright horder
    · have hleftCurrent :
          dramSenseCouplingCurrent nominalDramSenseCouplingInstance
              5 left (5 / 2) ≤ 0 := by
        rw [nominalDramSenseCouplingCurrent_eq_below
          hleftLower hleft]
        have hdelta : 0 ≤ 5 / 2 - left := by linarith
        exact neg_nonpos.mpr
          (add_nonneg
            (mul_nonneg (by norm_num) hdelta)
            (mul_nonneg (by norm_num) (sq_nonneg _)))
      have hrightCurrent :
          0 <
            dramSenseCouplingCurrent nominalDramSenseCouplingInstance
              5 right (5 / 2) := by
        rw [nominalDramSenseCouplingCurrent_eq_above
          (le_of_not_ge hright) hrightUpper]
        have hdelta : 0 < right - 5 / 2 := by linarith
        have hdeltaUpper : right - 5 / 2 ≤ 1 / 2 := by
          linarith
        nlinarith [mul_pos hdelta
          (show 0 < 9 - (right - 5 / 2) by linarith)]
      linarith
  · exact nominalDramSenseCouplingCurrent_strictMono_above
      (le_of_not_ge hleft) hrightUpper horder

/-- At the precharged latch state, a positive bitline/reference margin gives
a strictly positive true-minus-complement derivative. The reverse ordering
gives a strictly negative derivative. -/
theorem dramSenseCoupling_nominal_initial_direction
    {world : DramSenseCouplingWorld}
    {time bitline reference : ℝ}
    {derivative : VectorState DramSenseCouplingIndex}
    (hinstance :
      world.fabricated = nominalDramSenseCouplingInstance)
    (hsupply : world.environment.supply = 5)
    (hbitlineLower : 2 ≤ bitline)
    (hbitlineUpper : bitline ≤ 3)
    (hreferenceLower : 2 ≤ reference)
    (hreferenceUpper : reference ≤ 3)
    (hresidual :
      dramSenseCouplingDAE.residual world time
        (dramSenseCouplingInitialState bitline reference)
        derivative) :
    if reference < bitline then
      0 < derivative .trueLine - derivative .complementLine
    else if bitline < reference then
      derivative .trueLine - derivative .complementLine < 0
    else
      derivative .trueLine = derivative .complementLine := by
  change
    world.fabricated.bitlineCapacitance * derivative .bitline +
          dramSenseCouplingCurrent world.fabricated
            world.environment.supply bitline (5 / 2) = 0 ∧
      world.fabricated.trueCapacitance * derivative .trueLine -
          dramSenseCouplingCurrent world.fabricated
            world.environment.supply bitline (5 / 2) = 0 ∧
      world.fabricated.referenceCapacitance * derivative .reference +
          dramSenseCouplingCurrent world.fabricated
            world.environment.supply reference (5 / 2) = 0 ∧
      world.fabricated.complementCapacitance *
            derivative .complementLine -
          dramSenseCouplingCurrent world.fabricated
            world.environment.supply reference (5 / 2) = 0 at hresidual
  rw [hinstance, hsupply] at hresidual
  change
    (3 / 10000000000000 : ℝ) * derivative .bitline +
          dramSenseCouplingCurrent nominalDramSenseCouplingInstance
            5 bitline (5 / 2) = 0 ∧
      (3 / 10000000000000 : ℝ) * derivative .trueLine -
          dramSenseCouplingCurrent nominalDramSenseCouplingInstance
            5 bitline (5 / 2) = 0 ∧
      (3 / 10000000000000 : ℝ) * derivative .reference +
          dramSenseCouplingCurrent nominalDramSenseCouplingInstance
            5 reference (5 / 2) = 0 ∧
      (3 / 10000000000000 : ℝ) * derivative .complementLine -
          dramSenseCouplingCurrent nominalDramSenseCouplingInstance
            5 reference (5 / 2) = 0 at hresidual
  by_cases hpositive : reference < bitline
  · rw [if_pos hpositive]
    have hcurrent :=
      nominalDramSenseCouplingCurrent_strictMono
        hreferenceLower hbitlineUpper hpositive
    norm_num at hresidual
    nlinarith
  · rw [if_neg hpositive]
    by_cases hnegative : bitline < reference
    · rw [if_pos hnegative]
      have hcurrent :=
        nominalDramSenseCouplingCurrent_strictMono
          hbitlineLower hreferenceUpper hnegative
      norm_num at hresidual
      nlinarith
    · rw [if_neg hnegative]
      have hequal : bitline = reference := by
        linarith
      subst reference
      norm_num at hresidual
      linarith

end LeanModels.Spice
