import LeanModels.Spice.Dram1T1C

/-!
# Source-derived selected-cell write phase

This module models one selected 1T1C storage node while the write driver
clamps the wordline and bitline. The behavior contains only the initial
condition and capacitor/MOS1 KCL. In particular, it contains no endpoint,
logic threshold, or settling clause.

For the nominal unboosted write-one phase, the primitive current law reduces
to a quadratic field below the threshold-loss boundary and zero above it.
The exact `4 V` boundary is approached asymptotically; finite write
correctness must therefore be phrased as entry into a voltage band.
-/

namespace LeanModels.Spice

open LeanModels.Circuit Set MeasureTheory

structure DramWriteEnvironment where
  wordlineVoltage : ℝ
  bitlineVoltage : ℝ
  initialStorage : ℝ
  horizon : ℝ

structure DramWriteInstance where
  threshold : ℝ
  beta : ℝ
  storageCapacitance : ℝ

noncomputable def DramWriteInstance.mos1Params
    (device : DramWriteInstance) : Mos1Params :=
  { polarity := .nmos
    threshold := device.threshold
    beta := device.beta
    lambda := 0 }

noncomputable def Dram1T1CInstance.asDramWriteInstance
    (device : Dram1T1CInstance) : DramWriteInstance :=
  { threshold := device.threshold
    beta := device.beta
    storageCapacitance := device.storageCapacitance }

abbrev DramWriteWorld :=
  RunWorld DramWriteInstance DramWriteEnvironment Unit Unit

structure DramWriteBoundary where
  storageVoltage : DenseTrace ℝ

def DramWriteAdmissible (world : DramWriteWorld) : Prop :=
  0 < world.fabricated.threshold ∧
  0 < world.fabricated.beta ∧
  0 < world.fabricated.storageCapacitance ∧
  0 ≤ world.environment.horizon

/-- Storage-node voltage derivative obtained directly from capacitor KCL and
the bidirectional access-device terminal current. -/
noncomputable def dramWriteField
    (world : DramWriteWorld) (storage : ℝ) : ℝ :=
  -(mos1TerminalCurrent world.fabricated.mos1Params
      world.environment.wordlineVoltage storage
      world.environment.bitlineVoltage) /
    world.fabricated.storageCapacitance

noncomputable def dramWriteDAE : ScalarDAE DramWriteWorld where
  residual world _time storage derivative :=
    derivative = dramWriteField world storage

inductive DramWriteClause where
  | initialCondition
  | evolution
deriving Repr, DecidableEq

noncomputable def DramWriteProgram :
    EquationProgram DramWriteClause DramWriteWorld DramWriteBoundary Unit where
  origin
    | .initialCondition => .initialCondition "storage capacitor voltage"
    | .evolution => .evolution "selected 1T1C write DAE"
  equation clause world boundary _internal :=
    match clause with
    | .initialCondition =>
        boundary.storageVoltage 0 = world.environment.initialStorage
    | .evolution =>
        dramWriteDAE.ACBehavesOn world world.environment.horizon
          boundary.storageVoltage

noncomputable def DramWriteBehavior :
    Behavior DramWriteWorld DramWriteBoundary Unit :=
  DramWriteProgram.behavior

theorem dramWriteProgram_physicsOnly :
    DramWriteProgram.PhysicsOnly := by
  intro clause
  cases clause <;> rfl

theorem dramWriteEquationManifest :
    EquationManifest DramWriteProgram [] := by
  constructor
  · simp
  · intro contract hcontract
    rcases hcontract with ⟨clause, hclause⟩
    cases clause <;>
      simp [DramWriteProgram] at hclause ⊢

noncomputable def nominalDramWriteOneWorld
    (initialStorage horizon : ℝ) : DramWriteWorld :=
  deterministicWorld
    { threshold := 1
      beta := 1 / 10000
      storageCapacitance := 3 / 100000000000000 }
    { wordlineVoltage := 5
      bitlineVoltage := 5
      initialStorage
      horizon }

noncomputable def nominalDramWriteOneRate : ℝ :=
  5000000000 / 3

noncomputable def nominalDramWriteOneField (storage : ℝ) : ℝ :=
  if storage ≤ 4 then
    nominalDramWriteOneRate * (4 - storage) ^ 2
  else 0

/-- The complete nominal write-one field projected from the primitive,
source/drain-symmetric MOS1 current and capacitor KCL. -/
theorem dramWrite_nominal_write_one_field
    (storage : ℝ) :
    dramWriteField (nominalDramWriteOneWorld 0 0) storage =
      nominalDramWriteOneField storage := by
  unfold dramWriteField nominalDramWriteOneWorld
    nominalDramWriteOneField nominalDramWriteOneRate
    DramWriteInstance.mos1Params deterministicWorld
    mos1TerminalCurrent mos1ForwardCurrent
  norm_num
  split_ifs <;> nlinarith

theorem dramWrite_nominal_write_one_field_at
    (initialStorage horizon storage : ℝ) :
    dramWriteField
        (nominalDramWriteOneWorld initialStorage horizon) storage =
      nominalDramWriteOneField storage := by
  simpa [dramWriteField, nominalDramWriteOneWorld, deterministicWorld] using
    dramWrite_nominal_write_one_field storage

theorem nominalDramWriteOneField_continuous :
    Continuous nominalDramWriteOneField := by
  unfold nominalDramWriteOneField
  apply Continuous.if_le
    (by fun_prop) continuous_const continuous_id continuous_const
  intro storage hboundary
  simp only [id_eq] at hboundary
  subst storage
  simp

/-- Closed-form nominal write-one trajectory from an initial voltage at or
below the threshold-loss boundary. -/
noncomputable def nominalDramWriteOneTrace
    (initialStorage : ℝ) : DenseTrace ℝ :=
  fun time =>
    4 -
      (4 - initialStorage) /
        (1 + nominalDramWriteOneRate * (4 - initialStorage) * time)

theorem nominalDramWriteOneRate_pos :
    0 < nominalDramWriteOneRate := by
  norm_num [nominalDramWriteOneRate]

theorem nominalDramWriteOneTrace_initial (initialStorage : ℝ) :
    nominalDramWriteOneTrace initialStorage 0 = initialStorage := by
  simp [nominalDramWriteOneTrace]

theorem nominalDramWriteOneTrace_denominator_pos
    {initialStorage time : ℝ}
    (hinitial : initialStorage ≤ 4) (htime : 0 ≤ time) :
    0 <
      1 + nominalDramWriteOneRate * (4 - initialStorage) * time := by
  have hrate := nominalDramWriteOneRate_pos
  positivity

theorem nominalDramWriteOneTrace_le_target
    {initialStorage time : ℝ}
    (hinitial : initialStorage ≤ 4) (htime : 0 ≤ time) :
    nominalDramWriteOneTrace initialStorage time ≤ 4 := by
  have hdenom :=
    nominalDramWriteOneTrace_denominator_pos hinitial htime
  unfold nominalDramWriteOneTrace
  exact sub_le_self _ (div_nonneg (sub_nonneg.mpr hinitial) hdenom.le)

theorem nominalDramWriteOneTrace_mono_from_initial
    {initialStorage time : ℝ}
    (hinitial : initialStorage ≤ 4) (htime : 0 ≤ time) :
    initialStorage ≤ nominalDramWriteOneTrace initialStorage time := by
  have hrate := nominalDramWriteOneRate_pos
  have herror : 0 ≤ 4 - initialStorage := sub_nonneg.mpr hinitial
  have hdenom :=
    nominalDramWriteOneTrace_denominator_pos hinitial htime
  have hproduct :
      0 ≤ nominalDramWriteOneRate * (4 - initialStorage) * time :=
    mul_nonneg (mul_nonneg hrate.le herror) htime
  have hdivision :
      (4 - initialStorage) /
          (1 + nominalDramWriteOneRate * (4 - initialStorage) * time) ≤
        4 - initialStorage := by
    rw [div_le_iff₀ hdenom]
    nlinarith
  unfold nominalDramWriteOneTrace
  linarith

/-- Pointwise derivative of the closed-form write-one trajectory. -/
theorem nominalDramWriteOneTrace_hasDerivAt
    {initialStorage time : ℝ}
    (hinitial : initialStorage ≤ 4) (htime : 0 ≤ time) :
    HasDerivAt (nominalDramWriteOneTrace initialStorage)
      (nominalDramWriteOneRate *
        (4 - nominalDramWriteOneTrace initialStorage time) ^ 2)
      time := by
  let error : ℝ := 4 - initialStorage
  let denominator : ℝ :=
    1 + nominalDramWriteOneRate * error * time
  have hdenominator :
      denominator ≠ 0 := by
    apply ne_of_gt
    dsimp only [denominator, error]
    exact nominalDramWriteOneTrace_denominator_pos hinitial htime
  have hdenominatorDerivative :
      HasDerivAt
        (fun point =>
          1 + nominalDramWriteOneRate * error * point)
        (nominalDramWriteOneRate * error) time := by
    simpa [mul_assoc] using
      ((hasDerivAt_id time).const_mul
        (nominalDramWriteOneRate * error)).const_add 1
  have hquotient :=
    (hasDerivAt_const time error).div
      hdenominatorDerivative hdenominator
  have hraw :=
    (hasDerivAt_const time (4 : ℝ)).sub hquotient
  apply hraw.congr_deriv
  dsimp only [nominalDramWriteOneTrace, error, denominator] at *
  field_simp
  ring

theorem nominalDramWriteOneTrace_absolutelyContinuous
    {initialStorage horizon : ℝ}
    (hinitial : initialStorage ≤ 4) (hhorizon : 0 ≤ horizon) :
    AbsolutelyContinuousOnInterval
      (nominalDramWriteOneTrace initialStorage) 0 horizon := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  rw [uIcc_of_le hhorizon]
  unfold nominalDramWriteOneTrace
  apply ContDiffOn.sub contDiffOn_const
  apply ContDiffOn.div contDiffOn_const (by fun_prop)
  intro time htime
  exact
    (nominalDramWriteOneTrace_denominator_pos
      hinitial htime.1).ne'

/-- The closed-form trace is a smooth solution of the primitive selected-cell
write DAE throughout every nonnegative finite horizon. -/
theorem nominalDramWriteOneTrace_smooth
    {initialStorage horizon : ℝ}
    (hinitial : initialStorage ≤ 4) (hhorizon : 0 ≤ horizon) :
    dramWriteDAE.SmoothBehavesOn
      (nominalDramWriteOneWorld initialStorage horizon) horizon
      (nominalDramWriteOneTrace initialStorage) := by
  refine ⟨hhorizon, ?_⟩
  intro time htime0 htimeH
  let derivative :=
    nominalDramWriteOneRate *
      (4 - nominalDramWriteOneTrace initialStorage time) ^ 2
  refine ⟨derivative,
    nominalDramWriteOneTrace_hasDerivAt hinitial htime0, ?_⟩
  change derivative =
    dramWriteField
      (nominalDramWriteOneWorld initialStorage horizon)
      (nominalDramWriteOneTrace initialStorage time)
  have hfield :=
    dramWrite_nominal_write_one_field
      (nominalDramWriteOneTrace initialStorage time)
  have hfield' :
      dramWriteField
          (nominalDramWriteOneWorld initialStorage horizon)
          (nominalDramWriteOneTrace initialStorage time) =
        nominalDramWriteOneField
          (nominalDramWriteOneTrace initialStorage time) := by
    simpa [dramWriteField, nominalDramWriteOneWorld,
      deterministicWorld] using hfield
  have hle :=
    nominalDramWriteOneTrace_le_target hinitial htime0
  simpa [derivative, nominalDramWriteOneField, hle] using hfield'.symm

theorem nominalDramWriteOneTrace_physical
    {initialStorage horizon : ℝ}
    (hinitial : initialStorage ≤ 4) (hhorizon : 0 ≤ horizon) :
    dramWriteDAE.ACBehavesOn
      (nominalDramWriteOneWorld initialStorage horizon) horizon
      (nominalDramWriteOneTrace initialStorage) :=
  dramWriteDAE.acBehavesOn_of_smooth
    (nominalDramWriteOneTrace_absolutelyContinuous hinitial hhorizon)
    (nominalDramWriteOneTrace_smooth hinitial hhorizon)

/-- An absolutely-continuous nominal physical behavior satisfies the
source-derived pointwise ODE on its whole closed horizon. -/
theorem dramWrite_nominal_hasDerivWithinAt
    {initialStorage horizon time : ℝ}
    {trace : DenseTrace ℝ}
    (hbehavior :
      dramWriteDAE.ACBehavesOn
        (nominalDramWriteOneWorld initialStorage horizon) horizon trace)
    (htime : time ∈ Icc (0 : ℝ) horizon) :
    HasDerivWithinAt trace
      (nominalDramWriteOneField (trace time))
      (Icc (0 : ℝ) horizon) time := by
  let fieldTrace : ℝ → ℝ :=
    fun point => nominalDramWriteOneField (trace point)
  let primitive : ℝ → ℝ :=
    fun point => trace 0 + ∫ t in (0 : ℝ)..point, fieldTrace t
  have htraceContinuous :
      ContinuousOn trace (Icc (0 : ℝ) horizon) := by
    have hcontinuous := hbehavior.2.1.continuousOn
    rwa [uIcc_of_le hbehavior.1] at hcontinuous
  have hfieldTraceContinuous :
      ContinuousOn fieldTrace (Icc (0 : ℝ) horizon) := by
    exact nominalDramWriteOneField_continuous.continuousOn.comp
      htraceContinuous fun _point _hpoint => mem_univ _
  have hderivativeEq :
      ∀ᵐ point ∂volume.restrict (uIcc (0 : ℝ) horizon),
        deriv trace point = fieldTrace point := by
    filter_upwards [hbehavior.2.2] with point hpoint
    obtain ⟨derivative, htraceDerivative, hresidual⟩ := hpoint
    rw [htraceDerivative.deriv]
    change derivative =
      dramWriteField
        (nominalDramWriteOneWorld initialStorage horizon)
        (trace point) at hresidual
    exact hresidual.trans
      (dramWrite_nominal_write_one_field_at
        initialStorage horizon (trace point))
  have hderivativeEq' :
      ∀ᵐ point, point ∈ uIcc (0 : ℝ) horizon →
        deriv trace point = fieldTrace point :=
    ae_imp_of_ae_restrict hderivativeEq
  have htraceEqPrimitive :
      EqOn trace primitive (Icc (0 : ℝ) horizon) := by
    intro point hpoint
    have hsubinterval :
        uIcc (0 : ℝ) point ⊆ uIcc (0 : ℝ) horizon := by
      rw [uIcc_of_le hpoint.1, uIcc_of_le hbehavior.1]
      intro target htarget
      exact ⟨htarget.1, htarget.2.trans hpoint.2⟩
    have htraceACSub :
        AbsolutelyContinuousOnInterval trace 0 point :=
      hbehavior.2.1.mono hsubinterval
    have hintegrals :
        (∫ t in (0 : ℝ)..point, deriv trace t) =
          ∫ t in (0 : ℝ)..point, fieldTrace t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hderivativeEq'] with target htarget
      intro htargetInterval
      apply htarget
      exact hsubinterval (uIoc_subset_uIcc htargetInterval)
    have hfundamental := htraceACSub.integral_deriv_eq_sub
    dsimp only [primitive]
    rw [← hintegrals, hfundamental]
    ring
  have hfieldTraceIntegrable :
      IntervalIntegrable fieldTrace volume 0 time := by
    exact
      (hfieldTraceContinuous.mono
        (uIcc_subset_Icc ⟨le_rfl, hbehavior.1⟩ htime)).intervalIntegrable
  letI : Fact (time ∈ Icc (0 : ℝ) horizon) := ⟨htime⟩
  have hintegralDerivative :
      HasDerivWithinAt
        (fun point => ∫ t in (0 : ℝ)..point, fieldTrace t)
        (fieldTrace time) (Icc (0 : ℝ) horizon) time :=
    intervalIntegral.integral_hasDerivWithinAt_right
      hfieldTraceIntegrable
      (hfieldTraceContinuous
        |>.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc time)
      (hfieldTraceContinuous time htime)
  have hprimitiveDerivative :
      HasDerivWithinAt primitive (fieldTrace time)
        (Icc (0 : ℝ) horizon) time := by
    simpa only [primitive, zero_add] using
      hintegralDerivative.const_add (trace 0)
  exact hprimitiveDerivative.congr
    (fun point hpoint => htraceEqPrimitive hpoint)
    (htraceEqPrimitive htime)

private theorem dramWrite_lipschitzOnWith_Icc_union
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

noncomputable def nominalDramWriteOneFieldLipschitz
    (bound : ℝ) : NNReal :=
  (4000000000 * (|bound| + 4)).toNNReal

/-- The source-derived write-one field is Lipschitz on every bounded interval
containing the nominal rail and threshold-loss target. -/
theorem nominalDramWriteOneField_lipschitzOn
    {bound : ℝ} (hbound : 4 ≤ bound) :
    LipschitzOnWith (nominalDramWriteOneFieldLipschitz bound)
      nominalDramWriteOneField (Icc (-bound) bound) := by
  have hbound0 : 0 ≤ bound := by linarith
  let leftField : ℝ → ℝ := fun storage =>
    nominalDramWriteOneRate * (4 - storage) ^ 2
  have hleftPolynomial :
      LipschitzOnWith (nominalDramWriteOneFieldLipschitz bound)
        leftField (Icc (-bound) 4) := by
    apply
      (convex_Icc (-bound) (4 : ℝ))
        |>.lipschitzOnWith_of_nnnorm_deriv_le
    · intro storage _hstorage
      dsimp only [leftField]
      fun_prop
    · intro storage hstorage
      have hsub :
          HasDerivAt (fun x : ℝ => 4 - x) (-1) storage := by
        simpa using (hasDerivAt_id storage).const_sub (4 : ℝ)
      have hderiv :
          HasDerivAt leftField
            (-2 * nominalDramWriteOneRate * (4 - storage)) storage := by
        dsimp only [leftField]
        have hraw := (hsub.pow 2).const_mul nominalDramWriteOneRate
        apply hraw.congr_deriv
        ring
      rw [hderiv.deriv, ← NNReal.coe_le_coe]
      simp only [nominalDramWriteOneFieldLipschitz, coe_nnnorm]
      rw [Real.coe_toNNReal _ (by positivity)]
      rw [Real.norm_eq_abs]
      have hnonpos :
          -2 * nominalDramWriteOneRate * (4 - storage) ≤ 0 := by
        have hproduct :
            0 ≤ 2 * nominalDramWriteOneRate * (4 - storage) :=
          mul_nonneg
            (mul_nonneg (by norm_num) nominalDramWriteOneRate_pos.le)
            (sub_nonneg.mpr hstorage.2)
        nlinarith
      rw [abs_of_nonpos hnonpos, abs_of_nonneg hbound0]
      norm_num [nominalDramWriteOneRate] at *
      nlinarith
  have hleft :
      LipschitzOnWith (nominalDramWriteOneFieldLipschitz bound)
        nominalDramWriteOneField (Icc (-bound) 4) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxformula :
        nominalDramWriteOneField x = leftField x := by
      simp [nominalDramWriteOneField, leftField, hx.2]
    have hyformula :
        nominalDramWriteOneField y = leftField y := by
      simp [nominalDramWriteOneField, leftField, hy.2]
    rw [hxformula, hyformula]
    exact hleftPolynomial.dist_le_mul x hx y hy
  have hright :
      LipschitzOnWith (nominalDramWriteOneFieldLipschitz bound)
        nominalDramWriteOneField (Icc 4 bound) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxzero : nominalDramWriteOneField x = 0 := by
      unfold nominalDramWriteOneField
      by_cases hxeq : x = 4
      · subst x
        simp
      · rw [if_neg (fun hxle => hxeq (le_antisymm hxle hx.1))]
    have hyzero : nominalDramWriteOneField y = 0 := by
      unfold nominalDramWriteOneField
      by_cases hyeq : y = 4
      · subst y
        simp
      · rw [if_neg (fun hyle => hyeq (le_antisymm hyle hy.1))]
    rw [hxzero, hyzero]
    simpa using
      (mul_nonneg
        (NNReal.coe_nonneg (nominalDramWriteOneFieldLipschitz bound))
        (dist_nonneg : 0 ≤ dist x y))
  exact dramWrite_lipschitzOnWith_Icc_union
    (by linarith) hbound hleft hright

/-- Any two nominal physical write-one trajectories with the same initial
storage voltage coincide throughout their common finite horizon. -/
theorem dramWrite_nominal_determinate
    {initialStorage horizon time : ℝ}
    {first second : DenseTrace ℝ}
    (hfirst :
      dramWriteDAE.ACBehavesOn
        (nominalDramWriteOneWorld initialStorage horizon) horizon first)
    (hsecond :
      dramWriteDAE.ACBehavesOn
        (nominalDramWriteOneWorld initialStorage horizon) horizon second)
    (hinitial : first 0 = second 0)
    (htime0 : 0 ≤ time) (htimeHorizon : time ≤ horizon) :
    first time = second time := by
  obtain ⟨firstBound, hfirstBound⟩ := hfirst.2.1.exists_bound
  obtain ⟨secondBound, hsecondBound⟩ := hsecond.2.1.exists_bound
  let bound : ℝ := max 4 (max firstBound secondBound)
  have hboundFour : 4 ≤ bound := le_max_left _ _
  have hfirstBoundLe : firstBound ≤ bound :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hsecondBoundLe : secondBound ≤ bound :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hfirstMem :
      ∀ point ∈ Icc (0 : ℝ) horizon,
        first point ∈ Icc (-bound) bound := by
    intro point hpoint
    have hnorm : ‖first point‖ ≤ firstBound := by
      apply hfirstBound point
      rwa [uIcc_of_le hfirst.1]
    have habs : |first point| ≤ bound := by
      rw [← Real.norm_eq_abs]
      exact hnorm.trans hfirstBoundLe
    exact abs_le.mp habs
  have hsecondMem :
      ∀ point ∈ Icc (0 : ℝ) horizon,
        second point ∈ Icc (-bound) bound := by
    intro point hpoint
    have hnorm : ‖second point‖ ≤ secondBound := by
      apply hsecondBound point
      rwa [uIcc_of_le hsecond.1]
    have habs : |second point| ≤ bound := by
      rw [← Real.norm_eq_abs]
      exact hnorm.trans hsecondBoundLe
    exact abs_le.mp habs
  have hfieldLipschitz :=
    nominalDramWriteOneField_lipschitzOn hboundFour
  have hfirstContinuous :
      ContinuousOn first (Icc (0 : ℝ) horizon) := by
    have hcontinuous := hfirst.2.1.continuousOn
    rwa [uIcc_of_le hfirst.1] at hcontinuous
  have hsecondContinuous :
      ContinuousOn second (Icc (0 : ℝ) horizon) := by
    have hcontinuous := hsecond.2.1.continuousOn
    rwa [uIcc_of_le hsecond.1] at hcontinuous
  have hfirstDerivative :
      ∀ point ∈ Ico (0 : ℝ) horizon,
        HasDerivWithinAt first
          (nominalDramWriteOneField (first point))
          (Ici point) point := by
    intro point hpoint
    exact
      ((dramWrite_nominal_hasDerivWithinAt
          hfirst ⟨hpoint.1, hpoint.2.le⟩)
        |>.mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGT_of_mem hpoint)).Ici_of_Ioi
  have hsecondDerivative :
      ∀ point ∈ Ico (0 : ℝ) horizon,
        HasDerivWithinAt second
          (nominalDramWriteOneField (second point))
          (Ici point) point := by
    intro point hpoint
    exact
      ((dramWrite_nominal_hasDerivWithinAt
          hsecond ⟨hpoint.1, hpoint.2.le⟩)
        |>.mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGT_of_mem hpoint)).Ici_of_Ioi
  have hequal : EqOn first second (Icc (0 : ℝ) horizon) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _point value => nominalDramWriteOneField value)
      (s := fun _point => Icc (-bound) bound)
      (K := nominalDramWriteOneFieldLipschitz bound)
    · intro _point _hpoint
      exact hfieldLipschitz
    · exact hfirstContinuous
    · exact hfirstDerivative
    · intro point hpoint
      exact hfirstMem point ⟨hpoint.1, hpoint.2.le⟩
    · exact hsecondContinuous
    · exact hsecondDerivative
    · intro point hpoint
      exact hsecondMem point ⟨hpoint.1, hpoint.2.le⟩
    · exact hinitial
  exact hequal ⟨htime0, htimeHorizon⟩

/-- A physical nominal write-one behavior exists for every initial storage
voltage at or below the threshold-loss boundary and every finite horizon. -/
theorem nominalDramWriteOne_realizable
    {initialStorage horizon : ℝ}
    (hinitial : initialStorage ≤ 4) (hhorizon : 0 ≤ horizon) :
    ∃ boundary,
      DramWriteBehavior
        (nominalDramWriteOneWorld initialStorage horizon)
        boundary () := by
  refine ⟨⟨nominalDramWriteOneTrace initialStorage⟩, ?_⟩
  intro clause
  cases clause
  case initialCondition =>
    exact nominalDramWriteOneTrace_initial initialStorage
  case evolution =>
    exact nominalDramWriteOneTrace_physical hinitial hhorizon

/-- Every nominal physical behavior equals the closed-form trajectory. -/
theorem nominalDramWriteOne_behavior_eq_trace
    {initialStorage horizon : ℝ}
    {boundary : DramWriteBoundary}
    (hinitial : initialStorage ≤ 4) (hhorizon : 0 ≤ horizon)
    (hbehavior :
      DramWriteBehavior
        (nominalDramWriteOneWorld initialStorage horizon)
        boundary ()) :
    ∀ time ∈ Icc (0 : ℝ) horizon,
      boundary.storageVoltage time =
        nominalDramWriteOneTrace initialStorage time := by
  intro time htime
  apply dramWrite_nominal_determinate
    (hfirst := hbehavior .evolution)
    (hsecond :=
      nominalDramWriteOneTrace_physical hinitial hhorizon)
  · exact (hbehavior .initialCondition).trans
      (nominalDramWriteOneTrace_initial initialStorage).symm
  · exact htime.1
  · exact htime.2

end LeanModels.Spice
