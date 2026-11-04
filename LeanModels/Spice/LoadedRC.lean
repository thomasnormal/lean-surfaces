import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic
import LeanModels.Circuit

/-!
# Loaded RC transient semantics

The circuit is a source driving an output through a series resistor, with a
load resistor and capacitor from output to ground.  Its native transient view
is the continuous KCL DAE.  Backward Euler is exposed separately through the
generic `ScalarDAE` numerical relation.
-/

namespace LeanModels.Spice

open LeanModels.Circuit

/-- Nominal loaded-RC data recovered from an extracted SPICE deck. -/
structure LoadedRCNominal where
  sourceName : String
  seriesName : String
  loadName : String
  capacitorName : String
  inputNode : String
  outputNode : String
  supply : Rat
  seriesResistance : Rat
  loadResistance : Rat
  capacitance : Rat
deriving Repr, BEq, DecidableEq, Inhabited

def loadedRCTypedNodeName
    (circuit : DCCircuit) (node : LeanModels.Circuit.NodeId) : String :=
  circuit.nodeNames.getD node.index ""

/-- Recover the transient parameters from the same typed circuit produced by
the direct Lean SPICE frontend. The adapter checks the selected devices and
their complete four-element topology before exposing any values. -/
def DCCircuit.toLoadedRCNominal (circuit : DCCircuit)
    (sourceName seriesName loadName capacitorName : String) :
    Except String LoadedRCNominal := do
  if !circuit.isValid then
    throw "loaded RC circuit is structurally invalid"
  if circuit.devices.size != 4 then
    throw s!"loaded RC requires exactly four devices, found {circuit.devices.size}"
  if circuit.deviceNames !=
      #[sourceName, seriesName, loadName, capacitorName] then
    throw "loaded RC device names or order do not match the selected topology"
  let (source, series, load, capacitor) ←
    match circuit.devices.toList with
    | [source, series, load, capacitor] =>
        pure (source, series, load, capacitor)
    | _ => throw "loaded RC device table does not contain four devices"
  let (sourcePositive, sourceNegative, supply) ← match source with
    | .voltageSource _ positive negative value =>
        pure (positive, negative, value)
    | _ => throw s!"{sourceName} is not a voltage source"
  let (seriesPositive, seriesNegative, seriesResistance) ← match series with
    | .resistor _ positive negative value =>
        pure (positive, negative, value)
    | _ => throw s!"{seriesName} is not a resistor"
  let (loadPositive, loadNegative, loadResistance) ← match load with
    | .resistor _ positive negative value =>
        pure (positive, negative, value)
    | _ => throw s!"{loadName} is not a resistor"
  let (capacitorPositive, capacitorNegative, capacitance) ← match capacitor with
    | .capacitor _ positive negative value =>
        pure (positive, negative, value)
    | _ => throw s!"{capacitorName} is not a capacitor"
  if sourceNegative != circuit.ground then
    throw s!"{sourceName} is not ground-referenced"
  if seriesPositive != sourcePositive then
    throw s!"{seriesName} is not connected to the source node"
  if loadPositive != seriesNegative || loadNegative != circuit.ground then
    throw s!"{loadName} is not the output-to-ground load"
  if capacitorPositive != seriesNegative ||
      capacitorNegative != circuit.ground then
    throw s!"{capacitorName} is not the output-to-ground capacitor"
  pure
    { sourceName
      seriesName
      loadName
      capacitorName
      inputNode := loadedRCTypedNodeName circuit sourcePositive
      outputNode := loadedRCTypedNodeName circuit seriesNegative
      supply
      seriesResistance
      loadResistance
      capacitance }

/-- Values fixed for one fabricated loaded-RC instance. -/
structure LoadedRCInstance where
  seriesResistance : ℝ
  loadResistance : ℝ
  capacitance : ℝ

/-- One transient run: constant supply, initial capacitor voltage, and proof
horizon. -/
structure LoadedRCEnvironment where
  supply : ℝ
  initialVoltage : ℝ
  horizon : ℝ

abbrev LoadedRCWorld :=
  RunWorld LoadedRCInstance LoadedRCEnvironment Unit Unit

/-- Interpret exact source literals as real physical parameters for one run. -/
noncomputable def LoadedRCNominal.world (nominal : LoadedRCNominal)
    (initialVoltage horizon : ℝ) : LoadedRCWorld :=
  deterministicWorld
    { seriesResistance := nominal.seriesResistance
      loadResistance := nominal.loadResistance
      capacitance := nominal.capacitance }
    { supply := nominal.supply
      initialVoltage
      horizon }

/-- The observable output trace. -/
structure LoadedRCBoundary where
  outputVoltage : DenseTrace ℝ

/-- Positive component values and a nonnegative requested horizon. -/
def LoadedRCAdmissible (world : LoadedRCWorld) : Prop :=
  0 < world.fabricated.seriesResistance ∧
  0 < world.fabricated.loadResistance ∧
  0 < world.fabricated.capacitance ∧
  0 ≤ world.environment.horizon

/-- KCL residual:

`C dv/dt + (v - Vs)/Rseries + v/Rload = 0`.
-/
noncomputable def loadedRCDAE : ScalarDAE LoadedRCWorld where
  residual world _time value derivative :=
    world.fabricated.capacitance * derivative +
      (value - world.environment.supply) /
        world.fabricated.seriesResistance +
      value / world.fabricated.loadResistance = 0

/-- Native finite-horizon behavior: initial capacitor voltage plus the
absolutely-continuous KCL DAE, with the residual required almost everywhere.
-/
noncomputable def LoadedRCBehavior :
    Behavior LoadedRCWorld LoadedRCBoundary Unit :=
  fun world boundary _internal =>
    boundary.outputVoltage 0 = world.environment.initialVoltage ∧
    loadedRCDAE.ACBehavesOn world world.environment.horizon
      boundary.outputVoltage

/-- Loaded DC target after the capacitor current reaches zero. -/
noncomputable def loadedRCTarget (world : LoadedRCWorld) : ℝ :=
  world.environment.supply * world.fabricated.loadResistance /
    (world.fabricated.seriesResistance + world.fabricated.loadResistance)

/-- Positive decay rate `(1/Rseries + 1/Rload)/C`. -/
noncomputable def loadedRCRate (world : LoadedRCWorld) : ℝ :=
  (1 / world.fabricated.seriesResistance +
    1 / world.fabricated.loadResistance) /
      world.fabricated.capacitance

/-- Closed-form witness used to establish realizability and settling. -/
noncomputable def loadedRCTrace (world : LoadedRCWorld) : DenseTrace ℝ :=
  fun time =>
    loadedRCTarget world +
      (world.environment.initialVoltage - loadedRCTarget world) *
        Real.exp (-loadedRCRate world * time)

theorem loadedRCRate_pos {world : LoadedRCWorld}
    (hadmissible : LoadedRCAdmissible world) :
    0 < loadedRCRate world := by
  unfold loadedRCRate
  exact div_pos
    (add_pos (one_div_pos.mpr hadmissible.1)
      (one_div_pos.mpr hadmissible.2.1))
    hadmissible.2.2.1

theorem loadedRCTrace_hasDerivAt (world : LoadedRCWorld) (time : ℝ) :
    HasDerivAt (loadedRCTrace world)
      ((world.environment.initialVoltage - loadedRCTarget world) *
        (-loadedRCRate world) *
        Real.exp (-loadedRCRate world * time)) time := by
  change
    HasDerivAt
      (fun t =>
        loadedRCTarget world +
          (world.environment.initialVoltage - loadedRCTarget world) *
            Real.exp (-loadedRCRate world * t))
      ((world.environment.initialVoltage - loadedRCTarget world) *
        (-loadedRCRate world) *
        Real.exp (-loadedRCRate world * time)) time
  let inner : ℝ → ℝ := fun t => -loadedRCRate world * t
  have hinner :
      HasDerivAt inner (-loadedRCRate world) time := by
    simpa only [inner, id_eq, mul_one] using
      (hasDerivAt_id time).const_mul (-loadedRCRate world)
  have hexp :
      HasDerivAt (fun t => Real.exp (inner t))
        (Real.exp (inner time) * (-loadedRCRate world)) time :=
    (Real.hasDerivAt_exp (inner time)).comp time hinner
  have hscaled :=
    hexp.const_mul
      (world.environment.initialVoltage - loadedRCTarget world)
  have hshifted := hscaled.const_add (loadedRCTarget world)
  simpa only [inner, mul_assoc, mul_comm, mul_left_comm]
    using hshifted

/-- The closed-form exponential trajectory is absolutely continuous on every
finite interval. -/
theorem loadedRCTrace_absolutelyContinuous (world : LoadedRCWorld)
    (horizon : ℝ) :
    AbsolutelyContinuousOnInterval (loadedRCTrace world) 0 horizon := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  exact
    (contDiff_const.add
      (contDiff_const.mul
        (Real.contDiff_exp.comp
          (contDiff_const.mul contDiff_id)))).contDiffOn

/-- The analytic witness satisfies the physical DAE residual pointwise. -/
theorem loadedRCTrace_residual {world : LoadedRCWorld}
    (hadmissible : LoadedRCAdmissible world) (time : ℝ) :
    loadedRCDAE.residual world time (loadedRCTrace world time)
      ((world.environment.initialVoltage - loadedRCTarget world) *
        (-loadedRCRate world) *
        Real.exp (-loadedRCRate world * time)) := by
  unfold loadedRCDAE loadedRCTrace loadedRCTarget loadedRCRate
  have hseries0 : world.fabricated.seriesResistance ≠ 0 :=
    ne_of_gt hadmissible.1
  have hload0 : world.fabricated.loadResistance ≠ 0 :=
    ne_of_gt hadmissible.2.1
  have hcap0 : world.fabricated.capacitance ≠ 0 :=
    ne_of_gt hadmissible.2.2.1
  have hsum0 :
      world.fabricated.seriesResistance +
        world.fabricated.loadResistance ≠ 0 :=
    ne_of_gt (add_pos hadmissible.1 hadmissible.2.1)
  field_simp [hseries0, hload0, hcap0, hsum0]
  ring

/-- The explicit exponential trajectory is a behavior on every requested
finite horizon. -/
theorem loadedRC_trace_is_behavior {world : LoadedRCWorld}
    (hadmissible : LoadedRCAdmissible world) :
    LoadedRCBehavior world ⟨loadedRCTrace world⟩ () := by
  constructor
  · simp [loadedRCTrace]
  refine ⟨hadmissible.2.2.2,
    loadedRCTrace_absolutelyContinuous world
      world.environment.horizon, ?_⟩
  exact MeasureTheory.ae_restrict_of_forall_mem
    measurableSet_uIcc fun time _htime => by
    refine ⟨
      (world.environment.initialVoltage - loadedRCTarget world) *
        (-loadedRCRate world) *
        Real.exp (-loadedRCRate world * time),
      loadedRCTrace_hasDerivAt world time, ?_⟩
    exact loadedRCTrace_residual hadmissible time

/-- Finite-horizon continuous behaviors exist for every admissible run. -/
theorem loadedRC_realizable :
    RealizableUnder LoadedRCBehavior LoadedRCAdmissible := by
  intro world hadmissible
  exact ⟨⟨loadedRCTrace world⟩, (), loadedRC_trace_is_behavior hadmissible⟩

/-- The DAE directly supplies the first-order derivative equation. -/
theorem loadedRC_derivative_eq {world : LoadedRCWorld}
    (hadmissible : LoadedRCAdmissible world)
    {time value derivative : ℝ}
    (hresidual : loadedRCDAE.residual world time value derivative) :
    derivative = -loadedRCRate world * (value - loadedRCTarget world) := by
  change
    world.fabricated.capacitance * derivative +
      (value - world.environment.supply) /
        world.fabricated.seriesResistance +
      value / world.fabricated.loadResistance = 0 at hresidual
  unfold loadedRCRate loadedRCTarget
  have hseries0 : world.fabricated.seriesResistance ≠ 0 :=
    ne_of_gt hadmissible.1
  have hload0 : world.fabricated.loadResistance ≠ 0 :=
    ne_of_gt hadmissible.2.1
  have hcap0 : world.fabricated.capacitance ≠ 0 :=
    ne_of_gt hadmissible.2.2.1
  have hsum0 :
      world.fabricated.seriesResistance +
        world.fabricated.loadResistance ≠ 0 :=
    ne_of_gt (add_pos hadmissible.1 hadmissible.2.1)
  field_simp [hseries0, hload0, hcap0, hsum0] at hresidual ⊢
  ring_nf at hresidual ⊢
  linear_combination
    (world.fabricated.seriesResistance +
      world.fabricated.loadResistance) * hresidual

theorem loadedRC_residual_of_derivative_eq {world : LoadedRCWorld}
    (hadmissible : LoadedRCAdmissible world)
    {time value derivative : ℝ}
    (hderivative :
      derivative = -loadedRCRate world * (value - loadedRCTarget world)) :
    loadedRCDAE.residual world time value derivative := by
  change
    world.fabricated.capacitance * derivative +
      (value - world.environment.supply) /
        world.fabricated.seriesResistance +
      value / world.fabricated.loadResistance = 0
  rw [hderivative]
  unfold loadedRCRate loadedRCTarget
  have hseries0 : world.fabricated.seriesResistance ≠ 0 :=
    ne_of_gt hadmissible.1
  have hload0 : world.fabricated.loadResistance ≠ 0 :=
    ne_of_gt hadmissible.2.1
  have hcap0 : world.fabricated.capacitance ≠ 0 :=
    ne_of_gt hadmissible.2.2.1
  have hsum0 :
      world.fabricated.seriesResistance +
        world.fabricated.loadResistance ≠ 0 :=
    ne_of_gt (add_pos hadmissible.1 hadmissible.2.1)
  field_simp [hseries0, hload0, hcap0, hsum0]
  ring

/-- Uniqueness of the loaded-RC DAE on the requested horizon.

The integrating factor `exp(rate*t)` turns the error into a function with
zero derivative; the mean-value theorem therefore makes it constant.
-/
theorem loadedRC_behavior_eq_trace {world : LoadedRCWorld}
    {boundary : LoadedRCBoundary}
    (hadmissible : LoadedRCAdmissible world)
    (hbehavior : LoadedRCBehavior world boundary ())
    {time : ℝ} (htime0 : 0 ≤ time)
    (htimeH : time ≤ world.environment.horizon) :
    boundary.outputVoltage time = loadedRCTrace world time := by
  rcases hbehavior with
    ⟨hinitial, _hhorizon, htraceAC, hdae⟩
  let integrating : ℝ → ℝ := fun t =>
    Real.exp (loadedRCRate world * t) *
      (boundary.outputVoltage t - loadedRCTarget world)
  have hexpAC :
      AbsolutelyContinuousOnInterval
        (fun t => Real.exp (loadedRCRate world * t))
        0 world.environment.horizon := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    exact
      (Real.contDiff_exp.comp
        (contDiff_const.mul contDiff_id)).contDiffOn
  have hintegratingAC :
      AbsolutelyContinuousOnInterval integrating
        0 world.environment.horizon := by
    have htargetAC :
        AbsolutelyContinuousOnInterval
          (fun _time : ℝ => loadedRCTarget world)
          0 world.environment.horizon :=
      ContDiffOn.absolutelyContinuousOnInterval
        contDiff_const.contDiffOn
    exact hexpAC.mul (htraceAC.sub htargetAC)
  have hintegratingDeriv :
      ∀ᵐ t ∂MeasureTheory.volume.restrict
          (Set.uIcc (0 : ℝ) world.environment.horizon),
        HasDerivAt integrating 0 t := by
    filter_upwards [hdae] with t hpoint
    obtain ⟨derivative, htrace, hresidual⟩ := hpoint
    have hderivative :=
      loadedRC_derivative_eq hadmissible hresidual
    have hinner :
        HasDerivAt (fun x : ℝ => loadedRCRate world * x)
          (loadedRCRate world) t := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id t).const_mul (loadedRCRate world)
    have hexp :
        HasDerivAt
          (fun x => Real.exp (loadedRCRate world * x))
          (Real.exp (loadedRCRate world * t) *
            loadedRCRate world) t :=
      (Real.hasDerivAt_exp (loadedRCRate world * t)).comp t hinner
    have hproduct :=
      hexp.mul (htrace.sub_const (loadedRCTarget world))
    have hzero :
        (Real.exp (loadedRCRate world * t) *
              loadedRCRate world) *
            (boundary.outputVoltage t - loadedRCTarget world) +
          Real.exp (loadedRCRate world * t) * derivative = 0 := by
      rw [hderivative]
      ring
    exact hproduct.congr_deriv hzero
  have hintegratingDeriv' :
      ∀ᵐ t, t ∈ Set.uIcc (0 : ℝ) world.environment.horizon →
        HasDerivAt integrating 0 t :=
    MeasureTheory.ae_imp_of_ae_restrict hintegratingDeriv
  obtain ⟨constant, hconstantOn⟩ :=
    hintegratingAC.const_of_ae_hasDerivAt_zero
      hintegratingDeriv'
  have hconstant :
      integrating time = integrating 0 :=
    (hconstantOn time
      (by
        rw [Set.uIcc_of_le hadmissible.2.2.2]
        exact ⟨htime0, htimeH⟩)).trans
      (hconstantOn 0 (by simp)).symm
  dsimp [integrating] at hconstant
  rw [hinitial] at hconstant
  simp only [mul_zero, Real.exp_zero, one_mul] at hconstant
  unfold loadedRCTrace
  have hexp0 :
      Real.exp (loadedRCRate world * time) ≠ 0 :=
    (Real.exp_pos _).ne'
  rw [show -loadedRCRate world * time =
    -(loadedRCRate world * time) by ring, Real.exp_neg]
  field_simp [hexp0]
  linear_combination hconstant

/-- Every finite-horizon behavior has the same observable voltage trace. -/
noncomputable def LoadedRCHorizonObservation (world : LoadedRCWorld)
    (boundary : LoadedRCBoundary) (_internal : Unit) : ℝ → Option ℝ :=
  fun time =>
    if 0 ≤ time ∧ time ≤ world.environment.horizon then
      some (boundary.outputVoltage time)
    else none

theorem loadedRC_determinate :
    DeterminateUnder LoadedRCBehavior LoadedRCAdmissible
      (ℝ → Option ℝ) LoadedRCHorizonObservation := by
  intro world hadmissible boundary₁ internal₁ boundary₂ internal₂
      hbehavior₁ hbehavior₂
  funext time
  change
    (if 0 ≤ time ∧ time ≤ world.environment.horizon then
      some (boundary₁.outputVoltage time) else none) =
    (if 0 ≤ time ∧ time ≤ world.environment.horizon then
      some (boundary₂.outputVoltage time) else none)
  by_cases htime : 0 ≤ time ∧ time ≤ world.environment.horizon
  · rw [if_pos htime, if_pos htime]
    exact congrArg some <|
      (loadedRC_behavior_eq_trace hadmissible hbehavior₁
      htime.1 htime.2).trans
      (loadedRC_behavior_eq_trace hadmissible hbehavior₂
        htime.1 htime.2).symm
  · simp [htime]

/-- Initial voltage lies below the target and both are nonnegative. -/
def LoadedRCSettlingAllowed (world : LoadedRCWorld) : Prop :=
  LoadedRCAdmissible world ∧
  0 ≤ world.environment.initialVoltage ∧
  world.environment.initialVoltage ≤ loadedRCTarget world

/-- Canonical charging traces never undershoot their initial voltage or
overshoot their DC target. -/
theorem loadedRCTrace_bounds {world : LoadedRCWorld}
    (hallowed : LoadedRCSettlingAllowed world)
    {time : ℝ} (htime0 : 0 ≤ time) :
    world.environment.initialVoltage ≤ loadedRCTrace world time ∧
    loadedRCTrace world time ≤ loadedRCTarget world := by
  rcases hallowed with ⟨hadmissible, hinitial0, hinitialTarget⟩
  have hrate := loadedRCRate_pos hadmissible
  have hexp0 : 0 ≤ Real.exp (-loadedRCRate world * time) :=
    (Real.exp_pos _).le
  have hexp1 : Real.exp (-loadedRCRate world * time) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hgap :
      0 ≤ loadedRCTarget world - world.environment.initialVoltage := by
    linarith
  have hscaled0 :
      0 ≤ (loadedRCTarget world - world.environment.initialVoltage) *
        Real.exp (-loadedRCRate world * time) :=
    mul_nonneg hgap hexp0
  have hscaled1 :
      (loadedRCTarget world - world.environment.initialVoltage) *
          Real.exp (-loadedRCRate world * time) ≤
        loadedRCTarget world - world.environment.initialVoltage := by
    simpa using mul_le_mul_of_nonneg_left hexp1 hgap
  unfold loadedRCTrace
  constructor <;> nlinarith

/-- Every physical DAE behavior stays between the initial voltage and target
throughout its requested horizon. -/
theorem loadedRC_no_overshoot :
    SafeUnder LoadedRCBehavior LoadedRCSettlingAllowed
      (fun world boundary _internal =>
        Throughout world.environment.horizon fun time =>
          world.environment.initialVoltage ≤ boundary.outputVoltage time ∧
          boundary.outputVoltage time ≤ loadedRCTarget world) := by
  intro world boundary internal hallowed hbehavior time htime0 htimeH
  rw [loadedRC_behavior_eq_trace hallowed.1 hbehavior htime0 htimeH]
  exact loadedRCTrace_bounds hallowed htime0

/-- Voltage envelope used as the compact model's validity domain. -/
def LoadedRCVoltageDomain (world : LoadedRCWorld)
    (boundary : LoadedRCBoundary) (_internal : Unit) : Prop :=
  Throughout world.environment.horizon fun time =>
    0 ≤ boundary.outputVoltage time ∧
    boundary.outputVoltage time ≤ loadedRCTarget world

/-- The physical trajectory cannot leave the nonnegative, no-overshoot
voltage domain on which the component model is claimed to apply. -/
theorem loadedRC_stays_in_validity_domain :
    StaysWithinValidityDomain LoadedRCBehavior LoadedRCSettlingAllowed
      LoadedRCVoltageDomain := by
  intro world boundary internal hallowed hbehavior
  have hbounds :=
    loadedRC_no_overshoot world boundary internal hallowed hbehavior
  intro time htime0 htimeH
  have hpoint := hbounds time htime0 htimeH
  exact ⟨le_trans hallowed.2.1 hpoint.1, hpoint.2⟩

/-- The canonical charging trace is monotone toward the target. -/
theorem loadedRCTrace_monotoneOn {world : LoadedRCWorld}
    (hallowed : LoadedRCSettlingAllowed world)
    {earlier later : ℝ} (htimes : earlier ≤ later) :
    loadedRCTrace world earlier ≤ loadedRCTrace world later := by
  rcases hallowed with ⟨hadmissible, _hinitial0, hinitialTarget⟩
  have hrate := loadedRCRate_pos hadmissible
  have hexp :
      Real.exp (-loadedRCRate world * later) ≤
        Real.exp (-loadedRCRate world * earlier) := by
    rw [Real.exp_le_exp]
    nlinarith
  have hcoefficient :
      world.environment.initialVoltage - loadedRCTarget world ≤ 0 := by
    linarith
  have hscaled :=
    mul_le_mul_of_nonpos_left hexp hcoefficient
  unfold loadedRCTrace
  linarith

/-- Every DAE behavior is monotone on its requested horizon. -/
theorem loadedRC_monotone {world : LoadedRCWorld}
    {boundary : LoadedRCBoundary}
    (hallowed : LoadedRCSettlingAllowed world)
    (hbehavior : LoadedRCBehavior world boundary ())
    {earlier later : ℝ} (hearlier0 : 0 ≤ earlier)
    (htimes : earlier ≤ later)
    (hlaterH : later ≤ world.environment.horizon) :
    boundary.outputVoltage earlier ≤ boundary.outputVoltage later := by
  rw [loadedRC_behavior_eq_trace hallowed.1 hbehavior
      hearlier0 (le_trans htimes hlaterH),
    loadedRC_behavior_eq_trace hallowed.1 hbehavior
      (le_trans hearlier0 htimes) hlaterH]
  exact loadedRCTrace_monotoneOn hallowed htimes

/-- Exact error envelope of the analytic trajectory. -/
theorem loadedRCTrace_error (world : LoadedRCWorld) (time : ℝ) :
    |loadedRCTrace world time - loadedRCTarget world| =
      |world.environment.initialVoltage - loadedRCTarget world| *
        Real.exp (-loadedRCRate world * time) := by
  unfold loadedRCTrace
  rw [show loadedRCTarget world +
      (world.environment.initialVoltage - loadedRCTarget world) *
          Real.exp (-loadedRCRate world * time) -
        loadedRCTarget world =
      (world.environment.initialVoltage - loadedRCTarget world) *
        Real.exp (-loadedRCRate world * time) by ring]
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]

/-- Explicit epsilon deadline for the continuous trajectory. -/
theorem loadedRCTrace_settles_by {world : LoadedRCWorld}
    (hadmissible : LoadedRCAdmissible world)
    {epsilon time : ℝ} (hepsilon : 0 < epsilon)
    (htime :
      Real.log
          (|world.environment.initialVoltage - loadedRCTarget world| /
            epsilon) /
        loadedRCRate world ≤ time) :
    |loadedRCTrace world time - loadedRCTarget world| ≤ epsilon := by
  rw [loadedRCTrace_error]
  let error :=
    |world.environment.initialVoltage - loadedRCTarget world|
  by_cases herror : error = 0
  · simp [error, herror, le_of_lt hepsilon]
  have herrorPos : 0 < error := lt_of_le_of_ne (abs_nonneg _) (Ne.symm herror)
  have hrate := loadedRCRate_pos hadmissible
  have hlog :
      Real.log (error / epsilon) ≤ loadedRCRate world * time := by
    have := (div_le_iff₀ hrate).mp htime
    nlinarith
  have hexp :
      Real.exp (-loadedRCRate world * time) ≤
        Real.exp (-Real.log (error / epsilon)) := by
    rw [Real.exp_le_exp]
    nlinarith
  have hratio : 0 < error / epsilon := div_pos herrorPos hepsilon
  rw [Real.exp_neg, Real.exp_log hratio] at hexp
  have hscaled := mul_le_mul_of_nonneg_left hexp herrorPos.le
  change error * Real.exp (-loadedRCRate world * time) ≤ epsilon
  calc
    error * Real.exp (-loadedRCRate world * time)
        ≤ error * (error / epsilon)⁻¹ := hscaled
    _ = epsilon := by
      field_simp [herrorPos.ne', hepsilon.ne']

/-- The same explicit deadline applies to every DAE behavior, not only the
constructed witness. -/
theorem loadedRC_settles_by {world : LoadedRCWorld}
    {boundary : LoadedRCBoundary}
    (hadmissible : LoadedRCAdmissible world)
    (hbehavior : LoadedRCBehavior world boundary ())
    {epsilon time : ℝ} (hepsilon : 0 < epsilon)
    (htime0 : 0 ≤ time)
    (htimeH : time ≤ world.environment.horizon)
    (hdeadline :
      Real.log
          (|world.environment.initialVoltage - loadedRCTarget world| /
            epsilon) /
        loadedRCRate world ≤ time) :
    |boundary.outputVoltage time - loadedRCTarget world| ≤ epsilon := by
  rw [loadedRC_behavior_eq_trace hadmissible hbehavior htime0 htimeH]
  exact loadedRCTrace_settles_by hadmissible hepsilon hdeadline

/-! ## Backward Euler: separate numerical semantics -/

/-- Closed-form solution of one implicit backward-Euler step. -/
noncomputable def loadedRCBackwardEulerNext
    (world : LoadedRCWorld) (step previous : ℝ) : ℝ :=
  loadedRCTarget world +
    (previous - loadedRCTarget world) /
      (1 + step * loadedRCRate world)

theorem loadedRCBackwardEulerNext_error
    (world : LoadedRCWorld) (step previous : ℝ) :
    loadedRCBackwardEulerNext world step previous -
        loadedRCTarget world =
      (previous - loadedRCTarget world) /
        (1 + step * loadedRCRate world) := by
  unfold loadedRCBackwardEulerNext
  ring

/-- The closed-form numerical update satisfies the generic backward-Euler
residual exactly. -/
theorem loadedRC_backwardEuler_is_step {world : LoadedRCWorld}
    (hadmissible : LoadedRCAdmissible world)
    {step time previous : ℝ} (hstep : 0 < step) :
    loadedRCDAE.BackwardEulerStep world step time previous
      (loadedRCBackwardEulerNext world step previous) := by
  constructor
  · exact hstep
  apply loadedRC_residual_of_derivative_eq hadmissible
  have hrate := loadedRCRate_pos hadmissible
  have hfactor :
      0 < 1 + step * loadedRCRate world := by
    nlinarith [mul_pos hstep hrate]
  unfold loadedRCBackwardEulerNext
  field_simp [ne_of_gt hstep, ne_of_gt hfactor]
  ring

/-- One numerical step moves a charging state monotonically toward the target
without overshoot. -/
theorem loadedRCBackwardEulerNext_bounds {world : LoadedRCWorld}
    (hadmissible : LoadedRCAdmissible world)
    {step previous : ℝ} (hstep : 0 < step)
    (hprevious : previous ≤ loadedRCTarget world) :
    previous ≤ loadedRCBackwardEulerNext world step previous ∧
    loadedRCBackwardEulerNext world step previous ≤ loadedRCTarget world := by
  have hrate := loadedRCRate_pos hadmissible
  have hfactor : 1 < 1 + step * loadedRCRate world := by
    nlinarith [mul_pos hstep hrate]
  have hinv0 : 0 ≤ (1 + step * loadedRCRate world)⁻¹ := by positivity
  have hinv1 : (1 + step * loadedRCRate world)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by linarith)]
    linarith
  have hgap : 0 ≤ loadedRCTarget world - previous := by linarith
  have hscaled0 :
      0 ≤ (loadedRCTarget world - previous) *
        (1 + step * loadedRCRate world)⁻¹ :=
    mul_nonneg hgap hinv0
  have hscaled1 :
      (loadedRCTarget world - previous) *
          (1 + step * loadedRCRate world)⁻¹ ≤
        loadedRCTarget world - previous := by
    simpa using mul_le_mul_of_nonneg_left hinv1 hgap
  unfold loadedRCBackwardEulerNext
  rw [div_eq_mul_inv]
  constructor <;> nlinarith

/-- Executable backward-Euler trajectory from an initial voltage. -/
noncomputable def loadedRCBackwardEulerTrace
    (world : LoadedRCWorld) (step initial : ℝ) : Nat → ℝ
  | 0 => initial
  | index + 1 =>
      loadedRCBackwardEulerNext world step
        (loadedRCBackwardEulerTrace world step initial index)

/-- Every prefix of the executable trajectory satisfies the numerical
semantics. -/
theorem loadedRC_backwardEuler_trajectory {world : LoadedRCWorld}
    (hadmissible : LoadedRCAdmissible world)
    {step initial : ℝ} (hstep : 0 < step) (steps : Nat) :
    loadedRCDAE.BackwardEulerTrajectory world step steps
      (loadedRCBackwardEulerTrace world step initial) := by
  constructor
  · exact hstep
  · intro index _hindex
    simpa only [loadedRCBackwardEulerTrace] using
      (loadedRC_backwardEuler_is_step hadmissible
        (time := index * step)
        (previous := loadedRCBackwardEulerTrace world step initial index)
        hstep)

/-- Every numerical iterate remains between its initial value and the target. -/
theorem loadedRCBackwardEulerTrace_bounds {world : LoadedRCWorld}
    (hadmissible : LoadedRCAdmissible world)
    {step initial : ℝ} (hstep : 0 < step)
    (hinitial : initial ≤ loadedRCTarget world) :
    ∀ index,
      initial ≤ loadedRCBackwardEulerTrace world step initial index ∧
      loadedRCBackwardEulerTrace world step initial index ≤
        loadedRCTarget world := by
  intro index
  induction index with
  | zero =>
      simp [loadedRCBackwardEulerTrace, hinitial]
  | succ index ih =>
      have hnext :=
        loadedRCBackwardEulerNext_bounds hadmissible hstep ih.2
      constructor
      · exact le_trans ih.1 hnext.1
      · exact hnext.2

end LeanModels.Spice

namespace LeanModels.Circuit

/-- Type-namespace wrapper so field notation on a directly parsed circuit
resolves without importing the legacy SPICE AST namespace. -/
def DCCircuit.toLoadedRCNominal (circuit : DCCircuit)
    (sourceName seriesName loadName capacitorName : String) :
    Except String LeanModels.Spice.LoadedRCNominal :=
  LeanModels.Spice.DCCircuit.toLoadedRCNominal circuit
    sourceName seriesName loadName capacitorName

def ElaboratedCircuit.toLoadedRCNominal
    (circuit : ElaboratedCircuit)
    (sourceName seriesName loadName capacitorName : String) :
    Except String LeanModels.Spice.LoadedRCNominal := do
  let projected ← circuit.toDCCircuit.mapError fun error =>
    s!"loaded RC exact-DC projection failed: {repr error}"
  projected.toLoadedRCNominal sourceName seriesName loadName capacitorName

end LeanModels.Circuit
