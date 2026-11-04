import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import LeanModels.Spice.DramArray
import LeanModels.Circuit.Equation

/-!
# Physical 1T1C cell contract

This module gives a selected DRAM cell and its bitline a two-state DAE.  The
only channel current is the source/drain-symmetric MOS1 terminal current; the
two capacitor equations are KCL.  Charge sharing is derived from those
equations rather than included in the behavior definition.
-/

namespace LeanModels.Spice

open LeanModels.Circuit Set MeasureTheory

inductive DramCellStateIndex
  | storage
  | bitline
deriving Repr, DecidableEq, BEq, Inhabited

structure DramCellInstance where
  threshold : ℝ
  beta : ℝ
  storageCapacitance : ℝ
  bitlineCapacitance : ℝ

structure DramCellEnvironment where
  wordlineVoltage : ℝ
  initialStorage : ℝ
  initialBitline : ℝ
  horizon : ℝ

abbrev DramCellWorld :=
  RunWorld DramCellInstance DramCellEnvironment Unit Unit

structure DramCellBoundary where
  voltage : VectorTrace DramCellStateIndex

def DramCellAdmissible (world : DramCellWorld) : Prop :=
  0 < world.fabricated.threshold ∧
  0 < world.fabricated.beta ∧
  0 < world.fabricated.storageCapacitance ∧
  0 < world.fabricated.bitlineCapacitance ∧
  0 ≤ world.environment.horizon

noncomputable def DramArrayLayout.cellInstance
    (layout : DramArrayLayout rows columns)
    (row : Fin rows) (column : Fin columns) : DramCellInstance :=
  { threshold := layout.threshold
    beta := layout.beta
    storageCapacitance :=
      (layout.cells row column).storageCapacitance
    bitlineCapacitance := layout.bitlineCapacitances column }

noncomputable def DramCellInstance.mos1Params
    (device : DramCellInstance) : Mos1Params :=
  { polarity := .nmos
    threshold := device.threshold
    beta := device.beta
    lambda := 0 }

/-- Nominal device values shared by the source-backed DRAM bank examples. -/
noncomputable def nominalDramCellDevice : DramCellInstance :=
  { threshold := 1
    beta := 1 / 10000
    storageCapacitance := 3 / 100000000000000
    bitlineCapacitance := 3 / 10000000000000 }

/-- Restored cell/bitline equilibrium for the unboosted 5 V NMOS bank. -/
noncomputable def dramCellRestoredState
    (value : Bool) : VectorState DramCellStateIndex
  | .storage => if value then 4 else 0
  | .bitline => if value then 5 else 0

/-- Capacitor energy relative to one restored equilibrium. -/
noncomputable def dramCellRestoredEnergy
    (device : DramCellInstance) (value : Bool)
    (state : VectorState DramCellStateIndex) : ℝ :=
  device.storageCapacitance *
      (state .storage - dramCellRestoredState value .storage) ^ 2 / 2 +
    device.bitlineCapacitance *
      (state .bitline - dramCellRestoredState value .bitline) ^ 2 / 2

/-- Current leaving the storage node and entering the bitline. -/
noncomputable def dramCellAccessCurrent
    (world : DramCellWorld) (state : VectorState DramCellStateIndex) : ℝ :=
  mos1TerminalCurrent world.fabricated.mos1Params
    world.environment.wordlineVoltage
    (state .storage) (state .bitline)

/-- KCL for the storage capacitor and loaded bitline capacitor. -/
noncomputable def dramCellDAE :
    VectorDAE DramCellWorld DramCellStateIndex where
  residual world _time state derivative :=
    world.fabricated.storageCapacitance * derivative .storage +
        dramCellAccessCurrent world state = 0 ∧
      world.fabricated.bitlineCapacitance * derivative .bitline -
        dramCellAccessCurrent world state = 0

inductive DramCellClause where
  | initialStorage
  | initialBitline
  | evolution
deriving Repr, DecidableEq

noncomputable def DramCellProgram :
    EquationProgram DramCellClause DramCellWorld DramCellBoundary Unit where
  origin
    | .initialStorage => .initialCondition "storage capacitor voltage"
    | .initialBitline => .initialCondition "bitline capacitor voltage"
    | .evolution => .evolution "1T1C vector DAE"
  equation clause world boundary _internal :=
    match clause with
    | .initialStorage =>
        boundary.voltage 0 .storage = world.environment.initialStorage
    | .initialBitline =>
        boundary.voltage 0 .bitline = world.environment.initialBitline
    | .evolution =>
        dramCellDAE.ACBehavesOn world world.environment.horizon
          boundary.voltage

noncomputable def DramCellBehavior :
    Behavior DramCellWorld DramCellBoundary Unit :=
  DramCellProgram.behavior

theorem dramCellProgram_physicsOnly : DramCellProgram.PhysicsOnly := by
  unfold EquationProgram.PhysicsOnly
  intro clause
  cases clause <;> rfl

noncomputable def dramCellTotalCharge
    (device : DramCellInstance)
    (state : VectorState DramCellStateIndex) : ℝ :=
  device.storageCapacitance * state .storage +
    device.bitlineCapacitance * state .bitline

/-- The two KCL equations cancel the internal channel current exactly. -/
theorem dramCell_residual_conserves_charge
    {world : DramCellWorld} {time : ℝ}
    {state derivative : VectorState DramCellStateIndex}
    (hresidual : dramCellDAE.residual world time state derivative) :
    world.fabricated.storageCapacitance * derivative .storage +
      world.fabricated.bitlineCapacitance * derivative .bitline = 0 := by
  unfold dramCellDAE at hresidual
  linarith [hresidual.1, hresidual.2]

/-- Every physical DAE trajectory conserves total storage-plus-bitline charge
throughout its finite horizon. -/
theorem dramCell_behavior_conserves_charge
    {world : DramCellWorld} {boundary : DramCellBoundary}
    (hbehavior : DramCellBehavior world boundary ()) :
    ∀ time ∈ Icc 0 world.environment.horizon,
      dramCellTotalCharge world.fabricated (boundary.voltage time) =
        dramCellTotalCharge world.fabricated (boundary.voltage 0) := by
  intro target htarget
  let charge : ℝ → ℝ :=
    (fun time =>
      world.fabricated.storageCapacitance *
        boundary.voltage time .storage) +
    (fun time =>
      world.fabricated.bitlineCapacitance *
        boundary.voltage time .bitline)
  have hdae := hbehavior .evolution
  have hac : AbsolutelyContinuousOnInterval charge 0
      world.environment.horizon := by
    exact
      ((hdae.2.1 .storage).const_mul
        world.fabricated.storageCapacitance).add
      ((hdae.2.1 .bitline).const_mul
        world.fabricated.bitlineCapacitance)
  have hdae' :
      ∀ᵐ time,
        time ∈ uIcc 0 world.environment.horizon →
          ∃ derivative : VectorState DramCellStateIndex,
            (∀ index,
              HasDerivAt (fun t => boundary.voltage t index)
                (derivative index) time) ∧
            dramCellDAE.residual world time
              (boundary.voltage time) derivative :=
    (ae_restrict_iff' measurableSet_uIcc).mp hdae.2.2
  have hzero :
      ∀ᵐ time,
        time ∈ uIcc 0 world.environment.horizon →
          HasDerivAt charge 0 time := by
    filter_upwards [hdae'] with time htime hmem
    obtain ⟨derivative, hderivative, hresidual⟩ := htime hmem
    have hcharge :
        HasDerivAt charge
          (world.fabricated.storageCapacitance * derivative .storage +
          world.fabricated.bitlineCapacitance * derivative .bitline)
          time := by
      exact
        ((hderivative .storage).const_mul
          world.fabricated.storageCapacitance).add
        ((hderivative .bitline).const_mul
          world.fabricated.bitlineCapacitance)
    rw [dramCell_residual_conserves_charge hresidual] at hcharge
    exact hcharge
  obtain ⟨constant, hconstant⟩ :=
    hac.const_of_ae_hasDerivAt_zero hzero
  have htarget' :
      target ∈ uIcc 0 world.environment.horizon := by
    simpa [uIcc_of_le hdae.1] using htarget
  have hzero' :
      (0 : ℝ) ∈ uIcc 0 world.environment.horizon := by
    simp [uIcc_of_le hdae.1, hdae.1]
  change charge target = charge 0
  exact (hconstant target htarget').trans (hconstant 0 hzero').symm

/-- At either nominal restored state, the derivative of capacitor deviation
energy is nonpositive. For a stored zero this is ordinary MOS passivity. For
a stored one, charge conservation rules out motion into the apparent
threshold-dead region: below the `(4 V, 5 V)` point current restores the
state, while above 4 V the access channel is cut off. -/
theorem dramCell_nominal_restored_energy_rate_nonpos
    {world : DramCellWorld} {time : ℝ}
    {state derivative : VectorState DramCellStateIndex}
    (value : Bool)
    (hdevice : world.fabricated = nominalDramCellDevice)
    (hwordline : world.environment.wordlineVoltage = 5)
    (hresidual :
      dramCellDAE.residual world time state derivative)
    (hcharge :
      dramCellTotalCharge world.fabricated state =
        dramCellTotalCharge world.fabricated
          (dramCellRestoredState value)) :
    world.fabricated.storageCapacitance *
          (state .storage - dramCellRestoredState value .storage) *
          derivative .storage +
        world.fabricated.bitlineCapacitance *
          (state .bitline - dramCellRestoredState value .bitline) *
          derivative .bitline ≤
      0 := by
  let current :=
    mos1TerminalCurrent nominalDramCellDevice.mos1Params
      5 (state .storage) (state .bitline)
  have hresidual' :
      nominalDramCellDevice.storageCapacitance * derivative .storage +
            current = 0 ∧
        nominalDramCellDevice.bitlineCapacitance * derivative .bitline -
            current = 0 := by
    simpa [dramCellDAE, dramCellAccessCurrent, current, hdevice,
      hwordline] using hresidual
  have hrate :
      nominalDramCellDevice.storageCapacitance *
            (state .storage - dramCellRestoredState value .storage) *
            derivative .storage +
          nominalDramCellDevice.bitlineCapacitance *
            (state .bitline - dramCellRestoredState value .bitline) *
            derivative .bitline =
        current *
          ((state .bitline - dramCellRestoredState value .bitline) -
            (state .storage - dramCellRestoredState value .storage)) := by
    linear_combination
      (state .storage - dramCellRestoredState value .storage) *
          hresidual'.1 +
        (state .bitline - dramCellRestoredState value .bitline) *
          hresidual'.2
  rw [hdevice, hrate]
  cases hvalue : value
  · have hpassive :=
      mos1TerminalCurrent_nmos_mul_drop_nonneg
        (1 : ℝ) (1 / 10000) 5
        (state .storage) (state .bitline) (by norm_num)
    have hpassive' :
        0 ≤ current * (state .storage - state .bitline) := by
      simpa [current, nominalDramCellDevice,
        DramCellInstance.mos1Params] using hpassive
    simp only [hvalue, Bool.false_eq_true, ↓reduceIte,
      dramCellRestoredState, sub_zero]
    calc
      current * (state .bitline - state .storage) =
          -(current * (state .storage - state .bitline)) := by ring
      _ ≤ 0 := neg_nonpos.mpr hpassive'
  · simp only [hvalue, ↓reduceIte, dramCellRestoredState]
    change current *
      ((state .bitline - 5) - (state .storage - 4)) ≤ 0
    by_cases horder : state .bitline ≤ state .storage
    · have hcurrent :
          0 ≤ current := by
        exact mos1TerminalCurrent_nmos_nonneg_of_source_le_drain
          1 (1 / 10000) 5 (state .storage) (state .bitline)
          (by norm_num) horder
      exact mul_nonpos_of_nonneg_of_nonpos hcurrent (by linarith)
    · have hreverse : state .storage ≤ state .bitline :=
        le_of_not_ge horder
      by_cases hstorage : 4 ≤ state .storage
      · have hcurrent : current = 0 := by
          dsimp [current, nominalDramCellDevice,
            DramCellInstance.mos1Params]
          apply mos1TerminalCurrent_nmos_eq_zero_of_cutoff
          · linarith
          · linarith
        simp [hcurrent]
      · have hcharge' :
          nominalDramCellDevice.storageCapacitance * state .storage +
              nominalDramCellDevice.bitlineCapacitance * state .bitline =
            nominalDramCellDevice.storageCapacitance * 4 +
              nominalDramCellDevice.bitlineCapacitance * 5 := by
          simpa [hdevice, dramCellTotalCharge,
            dramCellRestoredState, hvalue] using hcharge
        have hbitline : 5 < state .bitline := by
          norm_num [nominalDramCellDevice] at hcharge'
          linarith
        have hcurrent :
            current ≤ 0 :=
          mos1TerminalCurrent_nmos_nonpos_of_drain_le_source
            1 (1 / 10000) 5 (state .storage) (state .bitline)
            (by norm_num) hreverse
        exact mul_nonpos_of_nonpos_of_nonneg hcurrent (by linarith)

/-- Every physical nominal cell/bitline trajectory starting at a restored
equilibrium remains there. This is an all-behavior theorem, not merely a
constant witness: charge conservation and MOS passivity make deviation
energy nonincreasing, while its initial value is already the global minimum
zero. -/
theorem dramCell_nominal_restored_preserved
    {world : DramCellWorld} {boundary : DramCellBoundary}
    (value : Bool)
    (hdevice : world.fabricated = nominalDramCellDevice)
    (hwordline : world.environment.wordlineVoltage = 5)
    (hinitialStorage :
      world.environment.initialStorage =
        dramCellRestoredState value .storage)
    (hinitialBitline :
      world.environment.initialBitline =
        dramCellRestoredState value .bitline)
    (hbehavior : DramCellBehavior world boundary ()) :
    ∀ time ∈ Icc 0 world.environment.horizon,
      boundary.voltage time = dramCellRestoredState value := by
  have hdae := hbehavior .evolution
  have hzeroState :
      boundary.voltage 0 = dramCellRestoredState value := by
    funext index
    cases index
    · exact (hbehavior .initialStorage).trans hinitialStorage
    · exact (hbehavior .initialBitline).trans hinitialBitline
  let storageDifference : ℝ → ℝ := fun time =>
    boundary.voltage time .storage -
      dramCellRestoredState value .storage
  let bitlineDifference : ℝ → ℝ := fun time =>
    boundary.voltage time .bitline -
      dramCellRestoredState value .bitline
  let energy : ℝ → ℝ := fun time =>
    (world.fabricated.storageCapacitance / 2) *
        storageDifference time ^ 2 +
      (world.fabricated.bitlineCapacitance / 2) *
        bitlineDifference time ^ 2
  let energyRate : ℝ → ℝ := fun time =>
    world.fabricated.storageCapacitance *
          storageDifference time * deriv storageDifference time +
      world.fabricated.bitlineCapacitance *
          bitlineDifference time * deriv bitlineDifference time
  have hstorageDifferenceAC :
      AbsolutelyContinuousOnInterval storageDifference 0
        world.environment.horizon := by
    exact (hdae.2.1 .storage).sub
      ((LipschitzWith.const
        (dramCellRestoredState value .storage)).lipschitzOnWith
        |>.absolutelyContinuousOnInterval)
  have hbitlineDifferenceAC :
      AbsolutelyContinuousOnInterval bitlineDifference 0
        world.environment.horizon := by
    exact (hdae.2.1 .bitline).sub
      ((LipschitzWith.const
        (dramCellRestoredState value .bitline)).lipschitzOnWith
        |>.absolutelyContinuousOnInterval)
  have hresidualAE := hdae.2.2
  rw [uIcc_of_le hdae.1] at hresidualAE
  have henergyRateNonpos :
      ∀ᵐ time ∂volume.restrict
          (Icc 0 world.environment.horizon),
        energyRate time ≤ 0 := by
    filter_upwards
      [hresidualAE,
        ae_restrict_mem (measurableSet_Icc :
          MeasurableSet (Icc 0 world.environment.horizon))]
      with time hpoint htime
    obtain ⟨derivative, hderivative, hresidual⟩ := hpoint
    have hcharge :=
      dramCell_behavior_conserves_charge hbehavior time htime
    rw [hzeroState] at hcharge
    have hrate :=
      dramCell_nominal_restored_energy_rate_nonpos value
        hdevice hwordline hresidual hcharge
    have hstorageDerivative :
        HasDerivAt storageDifference
          (derivative .storage) time :=
      (hderivative .storage).sub_const
        (dramCellRestoredState value .storage)
    have hbitlineDerivative :
        HasDerivAt bitlineDifference
          (derivative .bitline) time :=
      (hderivative .bitline).sub_const
        (dramCellRestoredState value .bitline)
    dsimp [energyRate]
    rw [hstorageDerivative.deriv, hbitlineDerivative.deriv]
    simpa [storageDifference, bitlineDifference] using hrate
  intro time htime
  have hstorageTargetAC :
      AbsolutelyContinuousOnInterval storageDifference 0 time :=
    hstorageDifferenceAC.mono (by
      rw [uIcc_of_le htime.1, uIcc_of_le hdae.1]
      exact Icc_subset_Icc le_rfl htime.2)
  have hbitlineTargetAC :
      AbsolutelyContinuousOnInterval bitlineDifference 0 time :=
    hbitlineDifferenceAC.mono (by
      rw [uIcc_of_le htime.1, uIcc_of_le hdae.1]
      exact Icc_subset_Icc le_rfl htime.2)
  have hmeasure :
      volume.restrict (Icc 0 time) ≤
        volume.restrict (Icc 0 world.environment.horizon) :=
    Measure.restrict_mono
      (Icc_subset_Icc le_rfl htime.2) le_rfl
  have henergyRateTarget :
      ∀ᵐ point ∂volume.restrict (Icc 0 time),
        energyRate point ≤ 0 :=
    henergyRateNonpos.filter_mono (ae_mono hmeasure)
  have hstorageRateIntegrable :
      IntervalIntegrable
        (fun point =>
          storageDifference point * deriv storageDifference point)
        volume 0 time :=
    hstorageTargetAC.intervalIntegrable_deriv.continuousOn_mul
      hstorageTargetAC.continuousOn
  have hbitlineRateIntegrable :
      IntervalIntegrable
        (fun point =>
          bitlineDifference point * deriv bitlineDifference point)
        volume 0 time :=
    hbitlineTargetAC.intervalIntegrable_deriv.continuousOn_mul
      hbitlineTargetAC.continuousOn
  have henergyRateIntegrable :
      IntervalIntegrable energyRate volume 0 time := by
    simpa only [energyRate, mul_assoc] using
      (hstorageRateIntegrable.const_mul
          world.fabricated.storageCapacitance).add
        (hbitlineRateIntegrable.const_mul
          world.fabricated.bitlineCapacitance)
  have hintegral :
      (∫ point in 0..time, energyRate point) ≤ 0 := by
    simpa using
      intervalIntegral.integral_mono_ae_restrict htime.1
        henergyRateIntegrable
        (intervalIntegrable_const :
          IntervalIntegrable (fun _point : ℝ => (0 : ℝ)) volume 0 time)
        henergyRateTarget
  have hstorageIntegral :
      2 *
          (∫ point in 0..time,
            storageDifference point * deriv storageDifference point) =
        storageDifference time ^ 2 - storageDifference 0 ^ 2 := by
    calc
      2 *
            (∫ point in 0..time,
              storageDifference point * deriv storageDifference point) =
          ∫ point in 0..time,
            2 * (storageDifference point * deriv storageDifference point) := by
              rw [intervalIntegral.integral_const_mul]
      _ =
          ∫ point in 0..time,
            deriv storageDifference point * storageDifference point +
              storageDifference point * deriv storageDifference point := by
              apply intervalIntegral.integral_congr
              intro point _hpoint
              ring
      _ =
          storageDifference time * storageDifference time -
            storageDifference 0 * storageDifference 0 :=
        hstorageTargetAC.integral_deriv_mul_eq_sub hstorageTargetAC
      _ =
          storageDifference time ^ 2 - storageDifference 0 ^ 2 := by
        ring
  have hbitlineIntegral :
      2 *
          (∫ point in 0..time,
            bitlineDifference point * deriv bitlineDifference point) =
        bitlineDifference time ^ 2 - bitlineDifference 0 ^ 2 := by
    calc
      2 *
            (∫ point in 0..time,
              bitlineDifference point * deriv bitlineDifference point) =
          ∫ point in 0..time,
            2 * (bitlineDifference point * deriv bitlineDifference point) := by
              rw [intervalIntegral.integral_const_mul]
      _ =
          ∫ point in 0..time,
            deriv bitlineDifference point * bitlineDifference point +
              bitlineDifference point * deriv bitlineDifference point := by
              apply intervalIntegral.integral_congr
              intro point _hpoint
              ring
      _ =
          bitlineDifference time * bitlineDifference time -
            bitlineDifference 0 * bitlineDifference 0 :=
        hbitlineTargetAC.integral_deriv_mul_eq_sub hbitlineTargetAC
      _ =
          bitlineDifference time ^ 2 - bitlineDifference 0 ^ 2 := by
        ring
  have henergyIntegral :
      (∫ point in 0..time, energyRate point) =
        energy time - energy 0 := by
    rw [show
      (∫ point in 0..time, energyRate point) =
          (∫ point in 0..time,
            world.fabricated.storageCapacitance *
              (storageDifference point * deriv storageDifference point)) +
          ∫ point in 0..time,
            world.fabricated.bitlineCapacitance *
              (bitlineDifference point * deriv bitlineDifference point) by
        simpa only [energyRate, mul_assoc] using
          intervalIntegral.integral_add
          (hstorageRateIntegrable.const_mul
            world.fabricated.storageCapacitance)
          (hbitlineRateIntegrable.const_mul
            world.fabricated.bitlineCapacitance)]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    dsimp [energy]
    linear_combination
      (world.fabricated.storageCapacitance / 2) * hstorageIntegral +
      (world.fabricated.bitlineCapacitance / 2) * hbitlineIntegral
  rw [henergyIntegral] at hintegral
  have henergyZero : energy 0 = 0 := by
    simp [energy, storageDifference, bitlineDifference, hzeroState]
  have henergyNonnegative : 0 ≤ energy time := by
    dsimp [energy]
    rw [hdevice]
    dsimp [nominalDramCellDevice]
    positivity
  have henergyEq : energy time = 0 := by
    linarith
  have henergyEq' :
      (nominalDramCellDevice.storageCapacitance / 2) *
            storageDifference time ^ 2 +
          (nominalDramCellDevice.bitlineCapacitance / 2) *
            bitlineDifference time ^ 2 =
        0 := by
    dsimp [energy] at henergyEq
    rw [hdevice] at henergyEq
    exact henergyEq
  have hstorageSquare :
      storageDifference time ^ 2 = 0 := by
    dsimp [nominalDramCellDevice] at henergyEq'
    nlinarith [sq_nonneg (storageDifference time),
      sq_nonneg (bitlineDifference time)]
  have hbitlineSquare :
      bitlineDifference time ^ 2 = 0 := by
    dsimp [nominalDramCellDevice] at henergyEq'
    nlinarith [sq_nonneg (storageDifference time),
      sq_nonneg (bitlineDifference time)]
  funext index
  cases index
  · dsimp [storageDifference] at hstorageSquare
    nlinarith
  · dsimp [bitlineDifference] at hbitlineSquare
    nlinarith

/-- The constant trajectory at a nominal restored state. -/
noncomputable def dramCellRestoredBoundary
    (value : Bool) : DramCellBoundary where
  voltage _time := dramCellRestoredState value

/-- Each nominal restored state is not only invariant but physically
realizable: its constant trajectory satisfies both capacitor KCL equations and
the bidirectional MOS1 channel law. -/
theorem dramCell_nominal_restored_realizable
    {world : DramCellWorld}
    (value : Bool)
    (hdevice : world.fabricated = nominalDramCellDevice)
    (hwordline : world.environment.wordlineVoltage = 5)
    (hinitialStorage :
      world.environment.initialStorage =
        dramCellRestoredState value .storage)
    (hinitialBitline :
      world.environment.initialBitline =
        dramCellRestoredState value .bitline)
    (hhorizon : 0 ≤ world.environment.horizon) :
    DramCellBehavior world (dramCellRestoredBoundary value) () := by
  change ∀ clause,
    DramCellProgram.equation clause world
      (dramCellRestoredBoundary value) ()
  intro clause
  cases clause
  case initialStorage =>
    change dramCellRestoredState value .storage =
      world.environment.initialStorage
    exact hinitialStorage.symm
  case initialBitline =>
    change dramCellRestoredState value .bitline =
      world.environment.initialBitline
    exact hinitialBitline.symm
  case evolution =>
    change dramCellDAE.ACBehavesOn world
      world.environment.horizon
      (dramCellRestoredBoundary value).voltage
    refine ⟨hhorizon, ?_, ?_⟩
    · intro index
      exact
        (LipschitzWith.const
          (dramCellRestoredState value index)).lipschitzOnWith
          |>.absolutelyContinuousOnInterval
    · exact ae_restrict_of_forall_mem measurableSet_uIcc
        (fun time _htime => by
          refine ⟨fun _index => 0, ?_, ?_⟩
          · intro index
            simpa [dramCellRestoredBoundary] using
              (hasDerivAt_const time
                (dramCellRestoredState value index))
          · cases hvalue : value <;>
              norm_num [dramCellDAE, dramCellAccessCurrent,
                dramCellRestoredBoundary, dramCellRestoredState,
                hdevice, hwordline, nominalDramCellDevice,
                DramCellInstance.mos1Params, mos1TerminalCurrent,
                mos1ForwardCurrent, hvalue])

/-- A channel below threshold carries no current in either source/drain
orientation. -/
theorem dramCellAccessCurrent_eq_zero_of_cutoff
    {world : DramCellWorld} {state : VectorState DramCellStateIndex}
    (hthreshold : 0 ≤ world.fabricated.threshold)
    (hgateStorage :
      world.environment.wordlineVoltage - state .storage ≤
        world.fabricated.threshold)
    (hgateBitline :
      world.environment.wordlineVoltage - state .bitline ≤
        world.fabricated.threshold) :
    dramCellAccessCurrent world state = 0 := by
  unfold dramCellAccessCurrent DramCellInstance.mos1Params
  simp only [mos1TerminalCurrent]
  by_cases horder : state .bitline ≤ state .storage
  · simp [horder, mos1ForwardCurrent, hgateBitline]
  · have hreverse : state .storage ≤ state .bitline := le_of_not_ge horder
    simp [horder, hreverse, mos1ForwardCurrent, hgateStorage]

theorem dramCell_hold_residual
    {world : DramCellWorld} {state : VectorState DramCellStateIndex}
    (hwordline : world.environment.wordlineVoltage = 0)
    (hstorage : 0 ≤ state .storage)
    (hbitline : 0 ≤ state .bitline)
    (hthreshold : 0 ≤ world.fabricated.threshold) :
    dramCellDAE.residual world 0 state (fun _ => 0) := by
  have hcurrent : dramCellAccessCurrent world state = 0 := by
    apply dramCellAccessCurrent_eq_zero_of_cutoff hthreshold
    · rw [hwordline]
      linarith
    · rw [hwordline]
      linarith
  simp [dramCellDAE, hcurrent]

/-- The closed, nonnegative hold state is inhabited.  This is the
non-vacuity witness for the zero-leakage MOS1 profile. -/
theorem dramCell_hold_realizable
    (world : DramCellWorld)
    (hadmissible : DramCellAdmissible world)
    (hwordline : world.environment.wordlineVoltage = 0)
    (hstorage : 0 ≤ world.environment.initialStorage)
    (hbitline : 0 ≤ world.environment.initialBitline) :
    ∃ boundary, DramCellBehavior world boundary () := by
  let trace : VectorTrace DramCellStateIndex :=
    fun _time index =>
      match index with
      | .storage => world.environment.initialStorage
      | .bitline => world.environment.initialBitline
  refine ⟨⟨trace⟩, ?_⟩
  intro clause
  cases clause
  case initialStorage => rfl
  case initialBitline => rfl
  case evolution =>
    refine ⟨hadmissible.2.2.2.2, ?_, ?_⟩
    · intro index
      exact (LipschitzWith.const (trace 0 index)).lipschitzOnWith
        |>.absolutelyContinuousOnInterval
    · exact ae_restrict_of_forall_mem measurableSet_uIcc fun time _htime => by
        refine ⟨fun _ => 0, ?_, ?_⟩
        · intro index
          cases index <;> exact hasDerivAt_const time _
        · apply dramCell_hold_residual hwordline
          · exact hstorage
          · exact hbitline
          · exact hadmissible.1.le

structure DramCellEndpoint where
  storage : ℝ
  bitline : ℝ

noncomputable def dramCellEndpointCharge
    (device : DramCellInstance) (state : DramCellEndpoint) : ℝ :=
  device.storageCapacitance * state.storage +
    device.bitlineCapacitance * state.bitline

def DramCellChargeConserved
    (device : DramCellInstance)
    (before after : DramCellEndpoint) : Prop :=
  dramCellEndpointCharge device after =
    dramCellEndpointCharge device before

def DramCellChannelSettled (state : DramCellEndpoint) : Prop :=
  state.storage = state.bitline

def DramCellSettledRead
    (device : DramCellInstance)
    (before after : DramCellEndpoint) : Prop :=
  DramCellChargeConserved device before after ∧
    DramCellChannelSettled after

noncomputable def dramCellSharedVoltage
    (device : DramCellInstance) (before : DramCellEndpoint) : ℝ :=
  dramCellEndpointCharge device before /
    (device.storageCapacitance + device.bitlineCapacitance)

noncomputable def dramCellSharedEndpoint
    (device : DramCellInstance) (before : DramCellEndpoint) :
    DramCellEndpoint :=
  { storage := dramCellSharedVoltage device before
    bitline := dramCellSharedVoltage device before }

/-- Charge conservation plus channel equilibration determines the shared
voltage; the closed form is not a premise of the behavior. -/
theorem dramCell_shared_voltage
    {device : DramCellInstance} {before after : DramCellEndpoint}
    (hstorageCap : 0 < device.storageCapacitance)
    (hbitlineCap : 0 < device.bitlineCapacitance)
    (hcharge : DramCellChargeConserved device before after)
    (hsettled : DramCellChannelSettled after) :
    after.storage = dramCellSharedVoltage device before ∧
      after.bitline = dramCellSharedVoltage device before := by
  have hsum :
      device.storageCapacitance + device.bitlineCapacitance ≠ 0 :=
    ne_of_gt (add_pos hstorageCap hbitlineCap)
  unfold DramCellChargeConserved dramCellEndpointCharge at hcharge
  unfold DramCellChannelSettled at hsettled
  unfold dramCellSharedVoltage dramCellEndpointCharge
  rw [← hsettled] at hcharge
  have hstorage :
      after.storage =
        (device.storageCapacitance * before.storage +
            device.bitlineCapacitance * before.bitline) /
          (device.storageCapacitance + device.bitlineCapacitance) := by
    apply (eq_div_iff hsum).2
    calc
      after.storage *
          (device.storageCapacitance + device.bitlineCapacitance) =
          device.storageCapacitance * after.storage +
            device.bitlineCapacitance * after.storage := by ring
      _ = device.storageCapacitance * before.storage +
            device.bitlineCapacitance * before.bitline := hcharge
  exact ⟨hstorage, by rw [← hsettled]; exact hstorage⟩

theorem dramCell_shared_endpoint_correct
    (device : DramCellInstance) (before : DramCellEndpoint)
    (hsum :
      device.storageCapacitance + device.bitlineCapacitance ≠ 0) :
    DramCellSettledRead device before
      (dramCellSharedEndpoint device before) := by
  refine ⟨?_, rfl⟩
  unfold DramCellChargeConserved dramCellEndpointCharge
  unfold dramCellSharedEndpoint dramCellSharedVoltage
    dramCellEndpointCharge
  dsimp
  field_simp [hsum]

/-- The settled endpoint contract is inhabited for every initial pair with
positive total capacitance.  This is endpoint non-vacuity; existence of a
continuous trajectory reaching the endpoint is a separate settling theorem. -/
theorem dramCell_settled_read_realizable
    (device : DramCellInstance) (before : DramCellEndpoint)
    (hsum :
      device.storageCapacitance + device.bitlineCapacitance ≠ 0) :
    ∃ after, DramCellSettledRead device before after :=
  ⟨dramCellSharedEndpoint device before,
    dramCell_shared_endpoint_correct device before hsum⟩

noncomputable def dramCellWriteOneTarget
    (supply wordline threshold : ℝ) : ℝ :=
  min supply (wordline - threshold)

theorem dramCell_write_one_target_unboosted
    {supply threshold : ℝ} (hthreshold : 0 ≤ threshold)
    (hthresholdSupply : threshold ≤ supply) :
    dramCellWriteOneTarget supply supply threshold =
      supply - threshold := by
  unfold dramCellWriteOneTarget
  rw [min_eq_right]
  linarith

theorem dramCell_write_one_target_boosted
    {supply threshold : ℝ} (hthreshold : 0 ≤ threshold) :
    dramCellWriteOneTarget supply (supply + threshold) threshold =
      supply := by
  unfold dramCellWriteOneTarget
  rw [min_eq_left]
  linarith

/-- At the threshold-limited write-one target the bidirectional MOS1 channel
current is exactly zero. -/
theorem dramCell_write_one_target_equilibrium
    (device : DramCellInstance) (supply wordline : ℝ)
    (hthreshold : 0 ≤ device.threshold)
    (htarget : 0 ≤ dramCellWriteOneTarget supply wordline device.threshold)
    (hsupply :
      dramCellWriteOneTarget supply wordline device.threshold ≤ supply) :
    mos1TerminalCurrent device.mos1Params wordline
        (dramCellWriteOneTarget supply wordline device.threshold) supply =
      0 := by
  unfold dramCellWriteOneTarget
  by_cases hsupplyTarget : supply ≤ wordline - device.threshold
  · rw [min_eq_left hsupplyTarget]
    simp [mos1TerminalCurrent, DramCellInstance.mos1Params,
      mos1ForwardCurrent_zero_drop]
  · have htargetSupply :
        wordline - device.threshold ≤ supply := le_of_not_ge hsupplyTarget
    rw [min_eq_right htargetSupply]
    have hcutoff : wordline - (wordline - device.threshold) ≤
        device.threshold := by linarith
    simp only [mos1TerminalCurrent, DramCellInstance.mos1Params]
    rw [if_neg hsupplyTarget]
    unfold mos1ForwardCurrent
    rw [if_pos hcutoff]
    simp

/-- With an unboosted NMOS pass device, cutoff does not select a unique
write-one voltage. Every storage voltage between the threshold-loss boundary
and the driven bitline is a zero-current equilibrium. -/
theorem dramCell_write_one_equilibrium_interval
    (device : DramCellInstance) (supply wordline storage : ℝ)
    (hlower : wordline - device.threshold ≤ storage)
    (hupper : storage ≤ supply) :
    mos1TerminalCurrent device.mos1Params wordline storage supply = 0 := by
  by_cases hsupplyStorage : supply ≤ storage
  · have hequal : storage = supply := le_antisymm hupper hsupplyStorage
    subst storage
    simp [mos1TerminalCurrent, DramCellInstance.mos1Params,
      mos1ForwardCurrent_zero_drop]
  · simp only [mos1TerminalCurrent, DramCellInstance.mos1Params,
      hsupplyStorage, if_false]
    unfold mos1ForwardCurrent
    rw [if_pos (by linarith)]
    simp

/-- The nominal unboosted write-one circuit has at least two distinct
equilibria. Static device equations therefore cannot justify an exact
`4 V` arrival claim; that claim needs trajectory and initial-state facts. -/
theorem dramCell_nominal_write_one_two_distinct_equilibria :
    mos1TerminalCurrent nominalDramCellDevice.mos1Params 5 4 5 = 0 ∧
      mos1TerminalCurrent nominalDramCellDevice.mos1Params 5 5 5 = 0 ∧
      (4 : ℝ) ≠ 5 := by
  constructor
  · apply dramCell_write_one_equilibrium_interval
    · norm_num [nominalDramCellDevice]
    · norm_num
  constructor
  · apply dramCell_write_one_equilibrium_interval
    · norm_num [nominalDramCellDevice]
    · norm_num
  · norm_num

end LeanModels.Spice
