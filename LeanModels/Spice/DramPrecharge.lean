import LeanModels.Spice.LoadedInverter
import LeanModels.Circuit.Equation

/-!
# Source-backed DRAM bitline precharge

The bank decks precharge each loaded bitline through one enabled NMOS whose
other channel terminal is connected to the external `vpre` reference.  This
module gives that device and the bitline capacitor a continuous-time
semantics.  The behavior contains only an initial condition and the physical
evolution law.  The nominal closed-form trajectory below is a proved witness,
not a clause of the behavior relation.

The first vertical slice covers charging from at or below the precharge
reference.  That is the operating condition exercised by the source
comparison harnesses.  Precharge from an arbitrary rail-valid prior state is
left as a separate extension rather than silently assumed.
-/

namespace LeanModels.Spice

open LeanModels.Circuit Set MeasureTheory

structure DramPrechargeInstance where
  threshold : ℝ
  beta : ℝ
  bitlineCapacitance : ℝ

structure DramPrechargeEnvironment where
  gateVoltage : ℝ
  referenceVoltage : ℝ
  initialVoltage : ℝ
  horizon : ℝ

abbrev DramPrechargeWorld :=
  RunWorld DramPrechargeInstance DramPrechargeEnvironment Unit Unit

structure DramPrechargeBoundary where
  bitlineVoltage : DenseTrace ℝ

def DramPrechargeAdmissible (world : DramPrechargeWorld) : Prop :=
  0 < world.fabricated.threshold ∧
  0 < world.fabricated.beta ∧
  0 < world.fabricated.bitlineCapacitance ∧
  0 ≤ world.environment.referenceVoltage ∧
  world.environment.referenceVoltage ≤
    world.environment.gateVoltage - world.fabricated.threshold ∧
  0 ≤ world.environment.initialVoltage ∧
  world.environment.initialVoltage ≤ world.environment.referenceVoltage ∧
  0 ≤ world.environment.horizon

noncomputable def DramPrechargeInstance.mos1Params
    (device : DramPrechargeInstance) : Mos1Params :=
  { polarity := .nmos
    threshold := device.threshold
    beta := device.beta
    lambda := 0 }

/-- Gate overdrive remaining when the bitline reaches the reference node. -/
noncomputable def dramPrechargeReferenceOverdrive
    (world : DramPrechargeWorld) : ℝ :=
  world.environment.gateVoltage -
    world.environment.referenceVoltage -
    world.fabricated.threshold

/-- A nonnegative voltage error used to extend the charging field beyond its
proved operating domain.  On `bitline ≤ reference` this is exactly the
reference-to-bitline drop. -/
noncomputable def dramPrechargeError
    (world : DramPrechargeWorld) (bitline : ℝ) : ℝ :=
  max 0 (world.environment.referenceVoltage - bitline)

/-- Globally defined charging field.

Inside the proved charging domain it is definitionally the square-law current
of the source-deck NMOS divided by the bitline capacitance.  Above the
reference the extension is zero; no theorem identifies that extension with
the physical device outside the declared domain. -/
noncomputable def dramPrechargeField
    (world : DramPrechargeWorld) (bitline : ℝ) : ℝ :=
  let error := dramPrechargeError world bitline
  world.fabricated.beta *
      (dramPrechargeReferenceOverdrive world * error + error ^ 2 / 2) /
    world.fabricated.bitlineCapacitance

noncomputable def dramPrechargeDAE :
    ScalarDAE DramPrechargeWorld where
  residual world _time bitline derivative :=
    derivative = dramPrechargeField world bitline

/-- Physical absolutely-continuous DAE behavior. -/
noncomputable def DramPrechargePhysicalBehavior :
    Behavior DramPrechargeWorld DramPrechargeBoundary Unit :=
  fun world boundary _internal =>
    boundary.bitlineVoltage 0 = world.environment.initialVoltage ∧
    dramPrechargeDAE.ACBehavesOn world world.environment.horizon
      boundary.bitlineVoltage

/-- Pointwise differentiable capability used by the current settling
automation. -/
noncomputable def DramPrechargeSmoothBehavior :
    Behavior DramPrechargeWorld DramPrechargeBoundary Unit :=
  fun world boundary _internal =>
    boundary.bitlineVoltage 0 = world.environment.initialVoltage ∧
    dramPrechargeDAE.SmoothBehavesOn world world.environment.horizon
      boundary.bitlineVoltage

inductive DramPrechargeClause where
  | initialCondition
  | evolution
deriving Repr, DecidableEq

/-- Every public precharge premise is classified.  The evolution clause
contains the absolutely-continuous physical DAE and the stronger smooth view
used by determinacy automation; neither contains an endpoint requirement. -/
noncomputable def DramPrechargeProgram :
    EquationProgram DramPrechargeClause DramPrechargeWorld
      DramPrechargeBoundary Unit where
  origin
    | .initialCondition => .initialCondition "bitline capacitor voltage"
    | .evolution =>
        .evolution "enabled MOS1 and bitline-capacitor precharge DAE"
  equation clause world boundary _internal :=
    match clause with
    | .initialCondition =>
        boundary.bitlineVoltage 0 = world.environment.initialVoltage
    | .evolution =>
        dramPrechargeDAE.ACBehavesOn world world.environment.horizon
            boundary.bitlineVoltage ∧
          dramPrechargeDAE.SmoothBehavesOn world world.environment.horizon
            boundary.bitlineVoltage

noncomputable def DramPrechargeBehavior :
    Behavior DramPrechargeWorld DramPrechargeBoundary Unit :=
  DramPrechargeProgram.behavior

theorem dramPrechargeProgram_physicsOnly :
    DramPrechargeProgram.PhysicsOnly := by
  intro clause
  cases clause <;> rfl

theorem dramPrechargeEquationManifest :
    EquationManifest DramPrechargeProgram [] := by
  constructor
  · simp
  · intro contract hcontract
    rcases hcontract with ⟨clause, hclause⟩
    cases clause <;> simp [DramPrechargeProgram] at hclause

/-- In the charging domain, the extended field is exactly capacitor KCL for
the enabled source-deck NMOS. -/
theorem dramPrechargeField_eq_mos1
    {world : DramPrechargeWorld} (hadmissible : DramPrechargeAdmissible world)
    {bitline : ℝ}
    (hbitline : bitline ≤ world.environment.referenceVoltage) :
    dramPrechargeField world bitline =
      -(mos1TerminalCurrent world.fabricated.mos1Params
          world.environment.gateVoltage bitline
          world.environment.referenceVoltage) /
        world.fabricated.bitlineCapacitance := by
  rcases hadmissible with
    ⟨hthreshold, hbeta, hcapacitance, hreference0, hgateReference,
      hinitial0, hinitialReference, hhorizon⟩
  by_cases hequal :
      bitline = world.environment.referenceVoltage
  · subst bitline
    simp [dramPrechargeField, dramPrechargeError,
      dramPrechargeReferenceOverdrive, mos1TerminalCurrent,
      DramPrechargeInstance.mos1Params,
      mos1ForwardCurrent_zero_drop]
  have hreferenceOrder :
      ¬ world.environment.referenceVoltage ≤ bitline := by
    intro hreverse
    exact hequal (le_antisymm hbitline hreverse)
  have hdrop0 :
      0 ≤ world.environment.referenceVoltage - bitline := by
    linarith
  have hoverdrive0 :
      0 ≤ dramPrechargeReferenceOverdrive world := by
    unfold dramPrechargeReferenceOverdrive
    linarith
  have hgate :
      world.environment.gateVoltage - bitline -
          world.fabricated.threshold =
        dramPrechargeReferenceOverdrive world +
          (world.environment.referenceVoltage - bitline) := by
    unfold dramPrechargeReferenceOverdrive
    ring
  simp only [dramPrechargeField, dramPrechargeError,
    max_eq_right hdrop0, mos1TerminalCurrent,
    DramPrechargeInstance.mos1Params, hreferenceOrder, if_false,
    neg_neg]
  rw [show
    world.environment.gateVoltage - bitline =
        (world.environment.gateVoltage - bitline -
          world.fabricated.threshold) + world.fabricated.threshold by ring]
  unfold mos1ForwardCurrent
  have hon :
      ¬ (world.environment.gateVoltage - bitline -
            world.fabricated.threshold) +
          world.fabricated.threshold ≤ world.fabricated.threshold := by
    linarith
  rw [if_neg hon]
  have htriode :
      world.environment.referenceVoltage - bitline ≤
        (world.environment.gateVoltage - bitline -
            world.fabricated.threshold) +
          world.fabricated.threshold - world.fabricated.threshold := by
    linarith
  rw [if_pos htriode]
  rw [hgate]
  ring

/-! ## Nominal source-deck trajectory -/

noncomputable def nominalDramPrechargeWorld
    (initialVoltage horizon : ℝ) : DramPrechargeWorld :=
  deterministicWorld
    { threshold := 1
      beta := 1 / 10000
      bitlineCapacitance := 3 / 10000000000000 }
    { gateVoltage := 5
      referenceVoltage := 5 / 2
      initialVoltage
      horizon }

noncomputable def nominalDramPrechargeDecayRate : ℝ :=
  500000000

noncomputable def nominalDramPrechargeInitialError
    (initialVoltage : ℝ) : ℝ :=
  5 / 2 - initialVoltage

noncomputable def nominalDramPrechargeExponential
    (time : ℝ) : ℝ :=
  Real.exp (time * -nominalDramPrechargeDecayRate)

noncomputable def nominalDramPrechargeDenominator
    (initialVoltage time : ℝ) : ℝ :=
  3 + nominalDramPrechargeInitialError initialVoltage *
    (1 - nominalDramPrechargeExponential time)

/-- Exact solution of the nominal source-derived charging DAE. -/
noncomputable def nominalDramPrechargeTrace
    (initialVoltage : ℝ) : DenseTrace ℝ :=
  fun time =>
    5 / 2 -
      3 * nominalDramPrechargeInitialError initialVoltage *
          nominalDramPrechargeExponential time /
        nominalDramPrechargeDenominator initialVoltage time

theorem nominalDramPrechargeDecayRate_pos :
    0 < nominalDramPrechargeDecayRate := by
  norm_num [nominalDramPrechargeDecayRate]

theorem nominalDramPrechargeExponential_pos (time : ℝ) :
    0 < nominalDramPrechargeExponential time := by
  exact Real.exp_pos _

theorem nominalDramPrechargeExponential_le_one
    {time : ℝ} (htime : 0 ≤ time) :
    nominalDramPrechargeExponential time ≤ 1 := by
  unfold nominalDramPrechargeExponential
  rw [Real.exp_le_one_iff]
  nlinarith [nominalDramPrechargeDecayRate_pos]

theorem nominalDramPrechargeDenominator_pos
    {initialVoltage time : ℝ}
    (hinitial : initialVoltage ≤ 5 / 2) (htime : 0 ≤ time) :
    0 < nominalDramPrechargeDenominator initialVoltage time := by
  have herror :
      0 ≤ nominalDramPrechargeInitialError initialVoltage := by
    unfold nominalDramPrechargeInitialError
    linarith
  have hexponential :
      0 ≤ 1 - nominalDramPrechargeExponential time := by
    linarith [nominalDramPrechargeExponential_le_one htime]
  unfold nominalDramPrechargeDenominator
  positivity

theorem nominalDramPrechargeTrace_initial (initialVoltage : ℝ) :
    nominalDramPrechargeTrace initialVoltage 0 = initialVoltage := by
  simp [nominalDramPrechargeTrace, nominalDramPrechargeDenominator,
    nominalDramPrechargeInitialError, nominalDramPrechargeExponential]

theorem nominalDramPrechargeTrace_le_reference
    {initialVoltage time : ℝ}
    (hinitial : initialVoltage ≤ 5 / 2) (htime : 0 ≤ time) :
    nominalDramPrechargeTrace initialVoltage time ≤ 5 / 2 := by
  have herror :
      0 ≤ nominalDramPrechargeInitialError initialVoltage := by
    unfold nominalDramPrechargeInitialError
    linarith
  have hdenominator :=
    nominalDramPrechargeDenominator_pos hinitial htime
  have hexponential :=
    (nominalDramPrechargeExponential_pos time).le
  unfold nominalDramPrechargeTrace
  exact sub_le_self _ (div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) herror) hexponential)
    hdenominator.le)

theorem nominalDramPrechargeTrace_error_nonneg
    {initialVoltage time : ℝ}
    (hinitial : initialVoltage ≤ 5 / 2) (htime : 0 ≤ time) :
    0 ≤ 5 / 2 - nominalDramPrechargeTrace initialVoltage time := by
  linarith [nominalDramPrechargeTrace_le_reference hinitial htime]

theorem nominalDramPrechargeTrace_error_eq
    (initialVoltage time : ℝ) :
    5 / 2 - nominalDramPrechargeTrace initialVoltage time =
      3 * nominalDramPrechargeInitialError initialVoltage *
          nominalDramPrechargeExponential time /
        nominalDramPrechargeDenominator initialVoltage time := by
  unfold nominalDramPrechargeTrace
  ring

theorem nominalDramPrechargeTrace_mono_from_initial
    {initialVoltage time : ℝ}
    (hinitial : initialVoltage ≤ 5 / 2) (htime : 0 ≤ time) :
    initialVoltage ≤ nominalDramPrechargeTrace initialVoltage time := by
  have herror :
      0 ≤ nominalDramPrechargeInitialError initialVoltage := by
    unfold nominalDramPrechargeInitialError
    linarith
  have hexponential0 :=
    (nominalDramPrechargeExponential_pos time).le
  have hexponential1 :=
    nominalDramPrechargeExponential_le_one htime
  have hdenominator :=
    nominalDramPrechargeDenominator_pos hinitial htime
  have hdenominatorLower :
      3 ≤ nominalDramPrechargeDenominator initialVoltage time := by
    unfold nominalDramPrechargeDenominator
    nlinarith [mul_nonneg herror (sub_nonneg.mpr hexponential1)]
  have hratio :
      3 * nominalDramPrechargeInitialError initialVoltage *
            nominalDramPrechargeExponential time /
          nominalDramPrechargeDenominator initialVoltage time ≤
        nominalDramPrechargeInitialError initialVoltage := by
    rw [div_le_iff₀ hdenominator]
    nlinarith [mul_nonneg herror hexponential0,
      mul_nonneg herror (sub_nonneg.mpr hexponential1)]
  rw [← nominalDramPrechargeTrace_error_eq] at hratio
  unfold nominalDramPrechargeInitialError at hratio
  linarith

/-- The exact nonlinear solution is bounded by the linearized exponential
error.  The omitted quadratic term only accelerates charging from below. -/
theorem nominalDramPrechargeTrace_error_le_exponential
    {initialVoltage time : ℝ}
    (hinitial : initialVoltage ≤ 5 / 2) (htime : 0 ≤ time) :
    5 / 2 - nominalDramPrechargeTrace initialVoltage time ≤
      nominalDramPrechargeInitialError initialVoltage *
        nominalDramPrechargeExponential time := by
  have herror :
      0 ≤ nominalDramPrechargeInitialError initialVoltage := by
    unfold nominalDramPrechargeInitialError
    linarith
  have hexponential :=
    (nominalDramPrechargeExponential_pos time).le
  have hdenominator :=
    nominalDramPrechargeDenominator_pos hinitial htime
  have hdenominatorLower :
      3 ≤ nominalDramPrechargeDenominator initialVoltage time := by
    unfold nominalDramPrechargeDenominator
    have hexponential1 :=
      nominalDramPrechargeExponential_le_one htime
    nlinarith [mul_nonneg herror (sub_nonneg.mpr hexponential1)]
  rw [nominalDramPrechargeTrace_error_eq]
  rw [div_le_iff₀ hdenominator]
  nlinarith [mul_nonneg herror hexponential]

theorem nominalDramPrechargeTrace_no_overshoot
    {initialVoltage horizon : ℝ}
    (hinitial0 : 0 ≤ initialVoltage)
    (hinitialReference : initialVoltage ≤ 5 / 2)
    (hhorizon : 0 ≤ horizon) :
    NoOvershoot (nominalDramPrechargeTrace initialVoltage)
      initialVoltage (5 / 2) horizon := by
  intro time htime0 _htimeH
  exact
    ⟨nominalDramPrechargeTrace_mono_from_initial
        hinitialReference htime0,
      nominalDramPrechargeTrace_le_reference
        hinitialReference htime0⟩

theorem nominalDramPrechargeTrace_settles_within
    {initialVoltage horizon tolerance deadline : ℝ}
    (hinitial0 : 0 ≤ initialVoltage)
    (hinitialReference : initialVoltage ≤ 5 / 2)
    (htolerance : 0 ≤ tolerance)
    (hdeadline0 : 0 ≤ deadline)
    (hdeadlineHorizon : deadline ≤ horizon)
    (hdeadline :
      nominalDramPrechargeInitialError initialVoltage *
          nominalDramPrechargeExponential deadline ≤ tolerance) :
    SettlesWithin (nominalDramPrechargeTrace initialVoltage)
      (5 / 2) tolerance deadline horizon := by
  refine ⟨htolerance, hdeadline0, hdeadlineHorizon, ?_⟩
  intro time hdeadlineTime htimeHorizon
  have htime0 : 0 ≤ time := hdeadline0.trans hdeadlineTime
  have herrorNonnegative :=
    nominalDramPrechargeTrace_error_nonneg
      hinitialReference htime0
  have herrorBound :=
    nominalDramPrechargeTrace_error_le_exponential
      hinitialReference htime0
  have hexponential :
      nominalDramPrechargeExponential time ≤
        nominalDramPrechargeExponential deadline := by
    unfold nominalDramPrechargeExponential
    apply Real.exp_le_exp.mpr
    nlinarith [nominalDramPrechargeDecayRate_pos]
  have hinitialError :
      0 ≤ nominalDramPrechargeInitialError initialVoltage := by
    unfold nominalDramPrechargeInitialError
    linarith
  have hbound :
      5 / 2 - nominalDramPrechargeTrace initialVoltage time ≤
        tolerance :=
    herrorBound.trans <|
      (mul_le_mul_of_nonneg_left hexponential hinitialError).trans hdeadline
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem nominalDramPrechargeTrace_hasDerivAt
    {initialVoltage time : ℝ}
    (hinitial : initialVoltage ≤ 5 / 2) (htime : 0 ≤ time) :
    HasDerivAt (nominalDramPrechargeTrace initialVoltage)
      (dramPrechargeField
        (nominalDramPrechargeWorld initialVoltage 0)
        (nominalDramPrechargeTrace initialVoltage time)) time := by
  let error := nominalDramPrechargeInitialError initialVoltage
  let exponential := nominalDramPrechargeExponential time
  let denominator := nominalDramPrechargeDenominator initialVoltage time
  have hdenominator :
      denominator ≠ 0 := by
    exact (nominalDramPrechargeDenominator_pos hinitial htime).ne'
  have hexponential :
      HasDerivAt nominalDramPrechargeExponential
        (-nominalDramPrechargeDecayRate * exponential) time := by
    have hlinear :
        HasDerivAt
          (fun point => point * -nominalDramPrechargeDecayRate)
          (-nominalDramPrechargeDecayRate) time := by
      exact hasDerivAt_mul_const (-nominalDramPrechargeDecayRate)
    have hraw := hlinear.exp
    change HasDerivAt
      (fun point =>
        Real.exp (point * -nominalDramPrechargeDecayRate))
      (-nominalDramPrechargeDecayRate *
        Real.exp (time * -nominalDramPrechargeDecayRate)) time
    simpa only [mul_comm] using hraw
  have hdenominatorDerivative :
      HasDerivAt
        (nominalDramPrechargeDenominator initialVoltage)
        (error * nominalDramPrechargeDecayRate * exponential) time := by
    have honeMinus :=
      (hasDerivAt_const time (1 : ℝ)).sub hexponential
    have hscaled := honeMinus.const_mul error
    have hbase := hscaled.const_add 3
    have hderivative :
        error * (0 - -nominalDramPrechargeDecayRate * exponential) =
          error * nominalDramPrechargeDecayRate * exponential := by
      ring
    apply (hbase.congr_deriv hderivative)
  have hnumerator :
      HasDerivAt
        (fun point =>
          3 * error * nominalDramPrechargeExponential point)
        (3 * error *
          (-nominalDramPrechargeDecayRate * exponential)) time := by
    convert hexponential.const_mul (3 * error) using 1 <;> ring
  have hquotient :=
    hnumerator.div hdenominatorDerivative hdenominator
  have hraw :=
    (hasDerivAt_const time (5 / 2 : ℝ)).sub hquotient
  apply hraw.congr_deriv
  have hmax :
      max 0
          (5 / 2 - nominalDramPrechargeTrace initialVoltage time) =
        5 / 2 - nominalDramPrechargeTrace initialVoltage time :=
    max_eq_right
      (nominalDramPrechargeTrace_error_nonneg hinitial htime)
  have herror :
      dramPrechargeError
          (nominalDramPrechargeWorld initialVoltage 0)
          (nominalDramPrechargeTrace initialVoltage time) =
        5 / 2 - nominalDramPrechargeTrace initialVoltage time := by
    change
      max 0
          (5 / 2 - nominalDramPrechargeTrace initialVoltage time) =
        5 / 2 - nominalDramPrechargeTrace initialVoltage time
    exact hmax
  unfold dramPrechargeField
  rw [herror]
  dsimp only [nominalDramPrechargeTrace,
    dramPrechargeReferenceOverdrive,
    nominalDramPrechargeWorld, deterministicWorld]
  dsimp only [error, exponential, denominator] at *
  norm_num [nominalDramPrechargeDecayRate] at *
  field_simp [hdenominator]
  ring

theorem nominalDramPrechargeTrace_absolutelyContinuous
    {initialVoltage horizon : ℝ}
    (hinitial : initialVoltage ≤ 5 / 2) (hhorizon : 0 ≤ horizon) :
    AbsolutelyContinuousOnInterval
      (nominalDramPrechargeTrace initialVoltage) 0 horizon := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  rw [uIcc_of_le hhorizon]
  unfold nominalDramPrechargeTrace
  apply ContDiffOn.sub contDiffOn_const
  apply ContDiffOn.div
  · unfold nominalDramPrechargeExponential
    fun_prop
  · unfold nominalDramPrechargeDenominator
    unfold nominalDramPrechargeExponential
    fun_prop
  · intro time htime
    exact
      (nominalDramPrechargeDenominator_pos hinitial htime.1).ne'

theorem nominalDramPrechargeTrace_smooth
    {initialVoltage horizon : ℝ}
    (hinitial : initialVoltage ≤ 5 / 2) (hhorizon : 0 ≤ horizon) :
    dramPrechargeDAE.SmoothBehavesOn
      (nominalDramPrechargeWorld initialVoltage horizon) horizon
      (nominalDramPrechargeTrace initialVoltage) := by
  refine ⟨hhorizon, ?_⟩
  intro time htime0 _htimeH
  refine ⟨dramPrechargeField
      (nominalDramPrechargeWorld initialVoltage horizon)
      (nominalDramPrechargeTrace initialVoltage time), ?_, rfl⟩
  have hderivative :=
    nominalDramPrechargeTrace_hasDerivAt hinitial htime0
  have hfield :
      dramPrechargeField
          (nominalDramPrechargeWorld initialVoltage horizon)
          (nominalDramPrechargeTrace initialVoltage time) =
        dramPrechargeField
          (nominalDramPrechargeWorld initialVoltage 0)
          (nominalDramPrechargeTrace initialVoltage time) := by
    unfold dramPrechargeField dramPrechargeError
      dramPrechargeReferenceOverdrive nominalDramPrechargeWorld
      deterministicWorld
    rfl
  rw [hfield]
  exact hderivative

theorem nominalDramPrechargeTrace_physical
    {initialVoltage horizon : ℝ}
    (hinitial : initialVoltage ≤ 5 / 2) (hhorizon : 0 ≤ horizon) :
    dramPrechargeDAE.ACBehavesOn
      (nominalDramPrechargeWorld initialVoltage horizon) horizon
      (nominalDramPrechargeTrace initialVoltage) :=
  dramPrechargeDAE.acBehavesOn_of_smooth
    (nominalDramPrechargeTrace_absolutelyContinuous hinitial hhorizon)
    (nominalDramPrechargeTrace_smooth hinitial hhorizon)

theorem nominalDramPrecharge_realizable
    {initialVoltage horizon : ℝ}
    (hinitial0 : 0 ≤ initialVoltage)
    (hinitialReference : initialVoltage ≤ 5 / 2)
    (hhorizon : 0 ≤ horizon) :
    ∃ boundary,
      DramPrechargeBehavior
        (nominalDramPrechargeWorld initialVoltage horizon)
        boundary () := by
  refine ⟨⟨nominalDramPrechargeTrace initialVoltage⟩, ?_⟩
  intro clause
  cases clause
  · exact nominalDramPrechargeTrace_initial initialVoltage
  · exact
      ⟨nominalDramPrechargeTrace_physical hinitialReference hhorizon,
        nominalDramPrechargeTrace_smooth hinitialReference hhorizon⟩

/-! ## Nominal determinacy and finite-time guarantee -/

noncomputable def nominalDramPrechargeField (bitline : ℝ) : ℝ :=
  dramPrechargeField (nominalDramPrechargeWorld 0 0) bitline

theorem dramPrechargeField_nominal
    (initialVoltage horizon bitline : ℝ) :
    dramPrechargeField
        (nominalDramPrechargeWorld initialVoltage horizon) bitline =
      nominalDramPrechargeField bitline := by
  unfold nominalDramPrechargeField dramPrechargeField
    dramPrechargeError dramPrechargeReferenceOverdrive
    nominalDramPrechargeWorld deterministicWorld
  rfl

noncomputable def nominalDramPrechargeFieldLipschitz
    (bound : ℝ) : NNReal :=
  (1000000000 * (|bound| + 5)).toNNReal

private theorem dramPrecharge_lipschitzOnWith_Icc_union
    {f : ℝ → ℝ} {K : NNReal} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hleft : LipschitzOnWith K f (Icc a b))
    (hright : LipschitzOnWith K f (Icc b c)) :
    LipschitzOnWith K f (Icc a c) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  wlog hxy : x ≤ y generalizing x y with h
  · rw [dist_comm (f x) (f y), dist_comm x y]
    exact h y hy x hx (le_of_not_ge hxy)
  by_cases hyb : y ≤ b
  · exact hleft.dist_le_mul x ⟨hx.1, hxy.trans hyb⟩
      y ⟨hy.1, hyb⟩
  by_cases hbx : b ≤ x
  · exact hright.dist_le_mul x ⟨hbx, hx.2⟩
      y ⟨hbx.trans hxy, hy.2⟩
  have hxb : x ≤ b := le_of_not_ge hbx
  have hby : b ≤ y := le_of_not_ge hyb
  calc
    dist (f x) (f y) ≤ dist (f x) (f b) + dist (f b) (f y) :=
      dist_triangle _ _ _
    _ ≤ K * dist x b + K * dist b y :=
      add_le_add
        (hleft.dist_le_mul x ⟨hx.1, hxb⟩ b ⟨hab, le_rfl⟩)
        (hright.dist_le_mul b ⟨le_rfl, hbc⟩ y ⟨hby, hy.2⟩)
    _ = K * dist x y := by
      simp only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxb),
        abs_of_nonpos (sub_nonpos.mpr hby),
        abs_of_nonpos (sub_nonpos.mpr hxy)]
      ring

theorem nominalDramPrechargeField_lipschitzOn
    {bound : ℝ} (hbound : 5 / 2 ≤ bound) :
    LipschitzOnWith (nominalDramPrechargeFieldLipschitz bound)
      nominalDramPrechargeField (Icc (-bound) bound) := by
  have hbound0 : 0 ≤ bound := by linarith
  let leftField : ℝ → ℝ := fun bitline =>
    (1 / 10000 : ℝ) *
        ((3 / 2) * (5 / 2 - bitline) +
          (5 / 2 - bitline) ^ 2 / 2) /
      (3 / 10000000000000)
  have hleftPolynomial :
      LipschitzOnWith (nominalDramPrechargeFieldLipschitz bound)
        leftField (Icc (-bound) (5 / 2)) := by
    apply
      (convex_Icc (-bound) (5 / 2 : ℝ))
        |>.lipschitzOnWith_of_nnnorm_deriv_le
    · intro bitline _hbitline
      dsimp only [leftField]
      fun_prop
    · intro bitline hbitline
      have hinner :
          HasDerivAt (fun x : ℝ => 5 / 2 - x) (-1) bitline := by
        simpa using (hasDerivAt_id bitline).const_sub (5 / 2 : ℝ)
      have hlinear :=
        hinner.const_mul (3 / 2 : ℝ)
      have hquadratic :=
        (hinner.pow 2).div_const 2
      have hsum := hlinear.add hquadratic
      have hraw :=
        (hsum.const_mul (1 / 10000 : ℝ)).div_const
          (3 / 10000000000000 : ℝ)
      have hderivative :
          HasDerivAt leftField
            (-(1000000000 / 3 : ℝ) * (4 - bitline)) bitline := by
        apply hraw.congr_deriv
        ring
      rw [hderivative.deriv, ← NNReal.coe_le_coe]
      simp only [nominalDramPrechargeFieldLipschitz, coe_nnnorm]
      rw [Real.coe_toNNReal _ (by positivity)]
      rw [Real.norm_eq_abs]
      have hfactor0 : 0 ≤ 4 - bitline := by
        linarith [hbitline.2]
      have hfactorBound : 4 - bitline ≤ |bound| + 5 := by
        rw [abs_of_nonneg hbound0]
        linarith [hbitline.1]
      rw [abs_of_nonpos (by
        have : 0 ≤ (1000000000 / 3 : ℝ) * (4 - bitline) :=
          mul_nonneg (by norm_num) hfactor0
        linarith)]
      nlinarith
  have hleft :
      LipschitzOnWith (nominalDramPrechargeFieldLipschitz bound)
        nominalDramPrechargeField (Icc (-bound) (5 / 2)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxformula :
        nominalDramPrechargeField x = leftField x := by
      have hxerror : 0 ≤ (5 / 2 : ℝ) - x := by
        linarith [hx.2]
      unfold nominalDramPrechargeField dramPrechargeField
        dramPrechargeError dramPrechargeReferenceOverdrive
        nominalDramPrechargeWorld deterministicWorld
      rw [max_eq_right hxerror]
      dsimp only [leftField]
      norm_num
    have hyformula :
        nominalDramPrechargeField y = leftField y := by
      have hyerror : 0 ≤ (5 / 2 : ℝ) - y := by
        linarith [hy.2]
      unfold nominalDramPrechargeField dramPrechargeField
        dramPrechargeError dramPrechargeReferenceOverdrive
        nominalDramPrechargeWorld deterministicWorld
      rw [max_eq_right hyerror]
      dsimp only [leftField]
      norm_num
    rw [hxformula, hyformula]
    exact hleftPolynomial.dist_le_mul x hx y hy
  have hright :
      LipschitzOnWith (nominalDramPrechargeFieldLipschitz bound)
        nominalDramPrechargeField (Icc (5 / 2) bound) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxzero : nominalDramPrechargeField x = 0 := by
      have hxerror : (5 / 2 : ℝ) - x ≤ 0 := by
        linarith [hx.1]
      unfold nominalDramPrechargeField dramPrechargeField
        dramPrechargeError dramPrechargeReferenceOverdrive
        nominalDramPrechargeWorld deterministicWorld
      rw [max_eq_left hxerror]
      norm_num
    have hyzero : nominalDramPrechargeField y = 0 := by
      have hyerror : (5 / 2 : ℝ) - y ≤ 0 := by
        linarith [hy.1]
      unfold nominalDramPrechargeField dramPrechargeField
        dramPrechargeError dramPrechargeReferenceOverdrive
        nominalDramPrechargeWorld deterministicWorld
      rw [max_eq_left hyerror]
      norm_num
    rw [hxzero, hyzero]
    simpa using
      (mul_nonneg
        (NNReal.coe_nonneg
          (nominalDramPrechargeFieldLipschitz bound))
        (dist_nonneg : 0 ≤ dist x y))
  exact dramPrecharge_lipschitzOnWith_Icc_union
    (by linarith) hbound hleft hright

/-- Any two nominal precharge behaviors with the same initial voltage agree
throughout their finite horizon.  This is derived from the locally Lipschitz
source-backed field, not included in the behavior definition. -/
theorem nominalDramPrecharge_determinate
    {initialVoltage horizon time : ℝ}
    {first second : DramPrechargeBoundary}
    (hfirst :
      DramPrechargeBehavior
        (nominalDramPrechargeWorld initialVoltage horizon) first ())
    (hsecond :
      DramPrechargeBehavior
        (nominalDramPrechargeWorld initialVoltage horizon) second ())
    (htime0 : 0 ≤ time) (htimeHorizon : time ≤ horizon) :
    first.bitlineVoltage time = second.bitlineVoltage time := by
  have hfirstEvolution := hfirst .evolution
  have hsecondEvolution := hsecond .evolution
  have hfirstInitial := hfirst .initialCondition
  have hsecondInitial := hsecond .initialCondition
  obtain ⟨firstBound, hfirstBound⟩ :=
    hfirstEvolution.1.2.1.exists_bound
  obtain ⟨secondBound, hsecondBound⟩ :=
    hsecondEvolution.1.2.1.exists_bound
  let bound : ℝ := max (5 / 2) (max firstBound secondBound)
  have hboundReference : 5 / 2 ≤ bound := le_max_left _ _
  have hfirstBoundLe : firstBound ≤ bound :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hsecondBoundLe : secondBound ≤ bound :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hfirstMem :
      ∀ point ∈ Icc (0 : ℝ) horizon,
        first.bitlineVoltage point ∈ Icc (-bound) bound := by
    intro point hpoint
    have hnorm : ‖first.bitlineVoltage point‖ ≤ firstBound := by
      apply hfirstBound point
      rwa [uIcc_of_le hfirstEvolution.1.1]
    have habs : |first.bitlineVoltage point| ≤ bound := by
      rw [← Real.norm_eq_abs]
      exact hnorm.trans hfirstBoundLe
    exact abs_le.mp habs
  have hsecondMem :
      ∀ point ∈ Icc (0 : ℝ) horizon,
        second.bitlineVoltage point ∈ Icc (-bound) bound := by
    intro point hpoint
    have hnorm : ‖second.bitlineVoltage point‖ ≤ secondBound := by
      apply hsecondBound point
      rwa [uIcc_of_le hsecondEvolution.1.1]
    have habs : |second.bitlineVoltage point| ≤ bound := by
      rw [← Real.norm_eq_abs]
      exact hnorm.trans hsecondBoundLe
    exact abs_le.mp habs
  have hfirstContinuous :
      ContinuousOn first.bitlineVoltage (Icc (0 : ℝ) horizon) := by
    have hcontinuous := hfirstEvolution.1.2.1.continuousOn
    rwa [uIcc_of_le hfirstEvolution.1.1] at hcontinuous
  have hsecondContinuous :
      ContinuousOn second.bitlineVoltage (Icc (0 : ℝ) horizon) := by
    have hcontinuous := hsecondEvolution.1.2.1.continuousOn
    rwa [uIcc_of_le hsecondEvolution.1.1] at hcontinuous
  have hfirstDerivative :
      ∀ point ∈ Ico (0 : ℝ) horizon,
        HasDerivWithinAt first.bitlineVoltage
          (nominalDramPrechargeField (first.bitlineVoltage point))
          (Ici point) point := by
    intro point hpoint
    obtain ⟨derivative, hderivative, hresidual⟩ :=
      hfirstEvolution.2.2 point hpoint.1 hpoint.2.le
    have hfield :
        derivative =
          nominalDramPrechargeField (first.bitlineVoltage point) := by
      simpa [dramPrechargeDAE,
        dramPrechargeField_nominal] using hresidual
    exact (hderivative.congr_deriv hfield).hasDerivWithinAt
  have hsecondDerivative :
      ∀ point ∈ Ico (0 : ℝ) horizon,
        HasDerivWithinAt second.bitlineVoltage
          (nominalDramPrechargeField (second.bitlineVoltage point))
          (Ici point) point := by
    intro point hpoint
    obtain ⟨derivative, hderivative, hresidual⟩ :=
      hsecondEvolution.2.2 point hpoint.1 hpoint.2.le
    have hfield :
        derivative =
          nominalDramPrechargeField (second.bitlineVoltage point) := by
      simpa [dramPrechargeDAE,
        dramPrechargeField_nominal] using hresidual
    exact (hderivative.congr_deriv hfield).hasDerivWithinAt
  have hequal :
      EqOn first.bitlineVoltage second.bitlineVoltage
        (Icc (0 : ℝ) horizon) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _point value => nominalDramPrechargeField value)
      (s := fun _point => Icc (-bound) bound)
      (K := nominalDramPrechargeFieldLipschitz bound)
    · intro _point _hpoint
      exact nominalDramPrechargeField_lipschitzOn hboundReference
    · exact hfirstContinuous
    · exact hfirstDerivative
    · intro point hpoint
      exact hfirstMem point ⟨hpoint.1, hpoint.2.le⟩
    · exact hsecondContinuous
    · exact hsecondDerivative
    · intro point hpoint
      exact hsecondMem point ⟨hpoint.1, hpoint.2.le⟩
    · exact hfirstInitial.trans hsecondInitial.symm
  exact hequal ⟨htime0, htimeHorizon⟩

theorem nominalDramPrecharge_behavior_eq_trace
    {initialVoltage horizon : ℝ}
    {boundary : DramPrechargeBoundary}
    (hinitial0 : 0 ≤ initialVoltage)
    (hinitialReference : initialVoltage ≤ 5 / 2)
    (hhorizon : 0 ≤ horizon)
    (hbehavior :
      DramPrechargeBehavior
        (nominalDramPrechargeWorld initialVoltage horizon)
        boundary ()) :
    ∀ time ∈ Icc (0 : ℝ) horizon,
      boundary.bitlineVoltage time =
        nominalDramPrechargeTrace initialVoltage time := by
  let canonical : DramPrechargeBoundary :=
    ⟨nominalDramPrechargeTrace initialVoltage⟩
  have hcanonical :
      DramPrechargeBehavior
        (nominalDramPrechargeWorld initialVoltage horizon)
        canonical () := by
    intro clause
    cases clause
    · exact nominalDramPrechargeTrace_initial initialVoltage
    · exact
        ⟨nominalDramPrechargeTrace_physical
            hinitialReference hhorizon,
          nominalDramPrechargeTrace_smooth
            hinitialReference hhorizon⟩
  intro time htime
  have heq :=
    nominalDramPrecharge_determinate hbehavior hcanonical
      htime.1 htime.2
  simpa [canonical] using heq

noncomputable def dramBankPrechargeHorizon : ℝ :=
  1 / 100000000

theorem nominalDramPrecharge_ten_ns_exponential :
    (5 / 2 : ℝ) * Real.exp (-5) ≤ 3 / 100 := by
  have hlower :=
    Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ 5 by norm_num) 10
  norm_num at hlower
  rw [Real.exp_neg]
  rw [mul_inv_le_iff₀ (Real.exp_pos 5)]
  nlinarith

theorem nominalDramPrecharge_zero_ten_ns_settles :
    SettlesWithin (nominalDramPrechargeTrace 0)
      (5 / 2) (3 / 100) dramBankPrechargeHorizon
      dramBankPrechargeHorizon := by
  apply nominalDramPrechargeTrace_settles_within
  · norm_num
  · norm_num
  · norm_num
  · norm_num [dramBankPrechargeHorizon]
  · exact le_rfl
  · norm_num [nominalDramPrechargeInitialError,
      nominalDramPrechargeExponential,
      nominalDramPrechargeDecayRate, dramBankPrechargeHorizon]
    exact nominalDramPrecharge_ten_ns_exponential

theorem nominalDramPrecharge_behavior_zero_ten_ns_settles
    {boundary : DramPrechargeBoundary}
    (hbehavior :
      DramPrechargeBehavior
        (nominalDramPrechargeWorld 0 dramBankPrechargeHorizon)
        boundary ()) :
    SettlesWithin boundary.bitlineVoltage
      (5 / 2) (3 / 100) dramBankPrechargeHorizon
      dramBankPrechargeHorizon := by
  have heq :=
    nominalDramPrecharge_behavior_eq_trace
      (initialVoltage := (0 : ℝ))
      (horizon := dramBankPrechargeHorizon)
      (boundary := boundary)
      (by norm_num) (by norm_num)
      (by norm_num [dramBankPrechargeHorizon]) hbehavior
  rcases nominalDramPrecharge_zero_ten_ns_settles with
    ⟨htolerance, hdeadline0, hdeadlineHorizon, hsettles⟩
  refine ⟨htolerance, hdeadline0, hdeadlineHorizon, ?_⟩
  intro time hdeadlineTime htimeHorizon
  rw [heq time ⟨hdeadline0.trans hdeadlineTime, htimeHorizon⟩]
  exact hsettles time hdeadlineTime htimeHorizon

end LeanModels.Spice
