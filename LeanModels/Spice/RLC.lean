import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic
import LeanModels.Circuit

/-!
# Source-backed series RLC transient semantics

The source circuit is a capacitor from `storage` to ground, an inductor from
`storage` to `load`, and a resistor from `load` to ground. The semantic state
contains two dynamic coordinates and one algebraic coordinate, so the example
exercises a vector DAE rather than three unrelated scalar ODEs.
-/

namespace LeanModels.Spice

open LeanModels.Circuit

/-- Parameters recovered from a checked three-device RLC topology. -/
structure RLCNominal where
  capacitorName : String
  inductorName : String
  resistorName : String
  storageNode : String
  loadNode : String
  capacitance : Rat
  inductance : Rat
  resistance : Rat
deriving Repr, BEq, DecidableEq, Inhabited

/-- Recover an RLC transient model from the same typed circuit produced by the
Lean SPICE frontend. The adapter checks the complete topology and orientations
before exposing parameters. -/
def DCCircuit.toRLCNominal (circuit : DCCircuit)
    (capacitorName inductorName resistorName : String) :
    Except String RLCNominal := do
  if !circuit.isValid then
    throw "RLC circuit is structurally invalid"
  if circuit.devices.size != 3 then
    throw s!"RLC circuit requires exactly three devices, found {circuit.devices.size}"
  if circuit.deviceNames != #[capacitorName, inductorName, resistorName] then
    throw "RLC device names or order do not match the selected topology"
  let (capacitor, inductor, resistor) ←
    match circuit.devices.toList with
    | [capacitor, inductor, resistor] =>
        pure (capacitor, inductor, resistor)
    | _ => throw "RLC device table does not contain three devices"
  let (storage, capacitorGround, capacitance) ← match capacitor with
    | .capacitor _ positive negative value =>
        pure (positive, negative, value)
    | _ => throw s!"{capacitorName} is not a capacitor"
  let (inductorPositive, load, inductance) ← match inductor with
    | .inductor _ positive negative value =>
        pure (positive, negative, value)
    | _ => throw s!"{inductorName} is not an inductor"
  let (resistorPositive, resistorGround, resistance) ← match resistor with
    | .resistor _ positive negative value =>
        pure (positive, negative, value)
    | _ => throw s!"{resistorName} is not a resistor"
  if capacitorGround != circuit.ground then
    throw s!"{capacitorName} is not ground-referenced"
  if inductorPositive != storage then
    throw s!"{inductorName} is not connected to the storage node"
  if resistorPositive != load || resistorGround != circuit.ground then
    throw s!"{resistorName} is not connected from the load node to ground"
  pure
    { capacitorName
      inductorName
      resistorName
      storageNode := circuit.nodeNames.getD storage.index ""
      loadNode := circuit.nodeNames.getD load.index ""
      capacitance
      inductance
      resistance }

structure RLCInstance where
  capacitance : ℝ
  inductance : ℝ
  resistance : ℝ

structure RLCEnvironment where
  initialVoltage : ℝ
  initialCurrent : ℝ
  horizon : ℝ

abbrev RLCWorld := RunWorld RLCInstance RLCEnvironment Unit Unit

noncomputable def RLCNominal.world (nominal : RLCNominal)
    (initialVoltage initialCurrent horizon : ℝ) : RLCWorld :=
  deterministicWorld
    { capacitance := nominal.capacitance
      inductance := nominal.inductance
      resistance := nominal.resistance }
    { initialVoltage, initialCurrent, horizon }

/-- Semantic state coordinates. `loadVoltage` is algebraic; its derivative is
not used by the residual. -/
inductive RLCVariable where
  | storageVoltage
  | inductorCurrent
  | loadVoltage
deriving Repr, BEq, DecidableEq, Inhabited

structure RLCBoundary where
  state : VectorTrace RLCVariable

def RLCAdmissible (world : RLCWorld) : Prop :=
  0 < world.fabricated.capacitance ∧
  0 < world.fabricated.inductance ∧
  0 < world.fabricated.resistance ∧
  0 ≤ world.environment.horizon

/-- The coupled physical equations:

* capacitor KCL: `C * dv/dt + i = 0`;
* inductor law: `L * di/dt = v - vload`;
* resistor law: `vload = R * i`.
-/
noncomputable def rlcDAE : VectorDAE RLCWorld RLCVariable where
  residual world _time value derivative :=
    world.fabricated.capacitance *
        derivative .storageVoltage +
          value .inductorCurrent = 0 ∧
    world.fabricated.inductance *
        derivative .inductorCurrent -
          (value .storageVoltage - value .loadVoltage) = 0 ∧
    value .loadVoltage -
        world.fabricated.resistance * value .inductorCurrent = 0

noncomputable def RLCBehavior :
    Behavior RLCWorld RLCBoundary Unit :=
  fun world boundary _internal =>
    boundary.state 0 .storageVoltage =
        world.environment.initialVoltage ∧
    boundary.state 0 .inductorCurrent =
        world.environment.initialCurrent ∧
    rlcDAE.ACBehavesOn world world.environment.horizon boundary.state

/-- Stored electromagnetic energy. The resistor stores no energy. -/
noncomputable def rlcEnergy (world : RLCWorld)
    (boundary : RLCBoundary) (time : ℝ) : ℝ :=
  world.fabricated.capacitance / 2 *
      (boundary.state time .storageVoltage *
        boundary.state time .storageVoltage) +
  world.fabricated.inductance / 2 *
      (boundary.state time .inductorCurrent *
        boundary.state time .inductorCurrent)

theorem rlcEnergy_hasDerivAt
    (world : RLCWorld) (boundary : RLCBoundary) (time : ℝ)
    (derivative : VectorState RLCVariable)
    (hderivative :
      ∀ index,
        HasDerivAt (fun t => boundary.state t index)
          (derivative index) time)
    (hresidual :
      rlcDAE.residual world time (boundary.state time) derivative) :
    HasDerivAt (rlcEnergy world boundary)
      (-world.fabricated.resistance *
        (boundary.state time .inductorCurrent) ^ 2) time := by
  have hv := hderivative RLCVariable.storageVoltage
  have hi := hderivative RLCVariable.inductorCurrent
  have henergy :=
    ((hv.mul hv).const_mul (world.fabricated.capacitance / 2)).add
      ((hi.mul hi).const_mul (world.fabricated.inductance / 2))
  have henergy' :=
    henergy.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by
        change
          rlcEnergy world boundary t =
            world.fabricated.capacitance / 2 *
                (boundary.state t .storageVoltage *
                  boundary.state t .storageVoltage) +
              world.fabricated.inductance / 2 *
                (boundary.state t .inductorCurrent *
                  boundary.state t .inductorCurrent)
        rfl)
  rcases hresidual with ⟨hcapacitor, hinductor, hresistor⟩
  have henergyDerivative :
      world.fabricated.capacitance / 2 *
            (derivative .storageVoltage *
                boundary.state time .storageVoltage +
              boundary.state time .storageVoltage *
                derivative .storageVoltage) +
          world.fabricated.inductance / 2 *
            (derivative .inductorCurrent *
                boundary.state time .inductorCurrent +
              boundary.state time .inductorCurrent *
                derivative .inductorCurrent) =
        -world.fabricated.resistance *
          (boundary.state time .inductorCurrent) ^ 2 := by
    linear_combination
      (boundary.state time .storageVoltage) * hcapacitor +
      (boundary.state time .inductorCurrent) * hinductor -
      (boundary.state time .inductorCurrent) * hresistor
  exact henergy'.congr_deriv henergyDerivative

/-- Absolute continuity of the electrical coordinates is preserved by the
quadratic stored-energy expression. -/
theorem rlcEnergy_absolutelyContinuous
    (world : RLCWorld) (boundary : RLCBoundary) (horizon : ℝ)
    (hcoordinates :
      ∀ index,
        AbsolutelyContinuousOnInterval
          (fun time => boundary.state time index) 0 horizon) :
    AbsolutelyContinuousOnInterval
      (rlcEnergy world boundary) 0 horizon := by
  have hv := hcoordinates RLCVariable.storageVoltage
  have hi := hcoordinates RLCVariable.inductorCurrent
  exact
    ((hv.mul hv).const_mul
      (world.fabricated.capacitance / 2)).add
    ((hi.mul hi).const_mul
      (world.fabricated.inductance / 2))

theorem rlcEnergy_antitoneOn
    {world : RLCWorld} {boundary : RLCBoundary}
    (hadmissible : RLCAdmissible world)
    (hbehavior : RLCBehavior world boundary ()) :
    AntitoneOn (rlcEnergy world boundary)
      (Set.Icc 0 world.environment.horizon) := by
  intro earlier hearlier later hlater htimes
  have henergyAC :=
    rlcEnergy_absolutelyContinuous world boundary
      world.environment.horizon hbehavior.2.2.2.1
  have hsubinterval :
      Set.uIcc earlier later ⊆
        Set.uIcc (0 : ℝ) world.environment.horizon := by
    rw [Set.uIcc_of_le htimes,
      Set.uIcc_of_le hadmissible.2.2.2]
    intro point hpoint
    exact ⟨le_trans hearlier.1 hpoint.1,
      le_trans hpoint.2 hlater.2⟩
  have henergyACSub :
      AbsolutelyContinuousOnInterval
        (rlcEnergy world boundary) earlier later :=
    henergyAC.mono hsubinterval
  have henergyDerivative :
      ∀ᵐ time ∂MeasureTheory.volume.restrict
          (Set.uIcc (0 : ℝ) world.environment.horizon),
        HasDerivAt (rlcEnergy world boundary)
          (-world.fabricated.resistance *
            (boundary.state time .inductorCurrent) ^ 2) time := by
    filter_upwards [hbehavior.2.2.2.2] with time hpoint
    obtain ⟨derivative, hcoordinates, hresidual⟩ := hpoint
    exact rlcEnergy_hasDerivAt world boundary time derivative
      hcoordinates hresidual
  have henergyDerivativeSub :
      ∀ᵐ time ∂MeasureTheory.volume.restrict
          (Set.Icc earlier later),
        HasDerivAt (rlcEnergy world boundary)
          (-world.fabricated.resistance *
            (boundary.state time .inductorCurrent) ^ 2) time := by
    rw [← Set.uIcc_of_le htimes]
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      hsubinterval henergyDerivative
  have hderivativeNonpositive :
      ∀ᵐ time ∂MeasureTheory.volume.restrict
          (Set.Icc earlier later),
        deriv (rlcEnergy world boundary) time ≤ 0 := by
    filter_upwards [henergyDerivativeSub] with time hderivative
    rw [hderivative.deriv]
    nlinarith [sq_nonneg
      (boundary.state time .inductorCurrent),
      hadmissible.2.2.1]
  have hintegral :
      (∫ time in earlier..later,
        deriv (rlcEnergy world boundary) time) ≤ 0 := by
    have hzero :
        IntervalIntegrable (fun _time : ℝ => (0 : ℝ))
          MeasureTheory.volume earlier later :=
      intervalIntegrable_const
    simpa using
      intervalIntegral.integral_mono_ae_restrict htimes
        henergyACSub.intervalIntegrable_deriv hzero
        hderivativeNonpositive
  rw [henergyACSub.integral_deriv_eq_sub] at hintegral
  linarith

/-- Every continuous solution dissipates stored energy. This permits ringing:
the theorem constrains the energy envelope, not each voltage's monotonicity. -/
theorem rlc_energy_dissipates
    {world : RLCWorld} {boundary : RLCBoundary}
    (hadmissible : RLCAdmissible world)
    (hbehavior : RLCBehavior world boundary ())
    {time : ℝ} (htime0 : 0 ≤ time)
    (htimeH : time ≤ world.environment.horizon) :
    rlcEnergy world boundary time ≤ rlcEnergy world boundary 0 :=
  rlcEnergy_antitoneOn hadmissible hbehavior
    ⟨le_rfl, hadmissible.2.2.2⟩
    ⟨htime0, htimeH⟩ htime0

/-! ## A non-vacuous critically damped family -/

noncomputable def rlcCriticalRate (world : RLCWorld) : ℝ :=
  world.fabricated.resistance / (2 * world.fabricated.inductance)

def RLCCriticallyDamped (world : RLCWorld) : Prop :=
  world.fabricated.resistance ^ 2 * world.fabricated.capacitance =
    4 * world.fabricated.inductance

noncomputable def rlcCriticalState (world : RLCWorld)
    (time : ℝ) (index : RLCVariable) : ℝ :=
  match index with
  | .storageVoltage =>
      world.environment.initialVoltage *
        (1 + rlcCriticalRate world * time) *
          Real.exp (-rlcCriticalRate world * time)
  | .inductorCurrent =>
      world.environment.initialVoltage *
        world.fabricated.capacitance *
        (rlcCriticalRate world) ^ 2 * time *
          Real.exp (-rlcCriticalRate world * time)
  | .loadVoltage =>
      world.fabricated.resistance *
        (world.environment.initialVoltage *
          world.fabricated.capacitance *
          (rlcCriticalRate world) ^ 2 * time *
            Real.exp (-rlcCriticalRate world * time))

noncomputable def rlcCriticalBoundary (world : RLCWorld) : RLCBoundary :=
  ⟨rlcCriticalState world⟩

/-- Every coordinate of the closed-form critical-damping trajectory is
absolutely continuous on a finite interval. -/
theorem rlcCriticalState_absolutelyContinuous
    (world : RLCWorld) (horizon : ℝ) (index : RLCVariable) :
    AbsolutelyContinuousOnInterval
      (fun time => rlcCriticalState world time index) 0 horizon := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  cases index <;> simp only [rlcCriticalState] <;> fun_prop

theorem rlcCriticalStorage_hasDerivAt (world : RLCWorld) (time : ℝ) :
    HasDerivAt
      (fun t => rlcCriticalState world t .storageVoltage)
      (-world.environment.initialVoltage *
        (rlcCriticalRate world) ^ 2 * time *
          Real.exp (-rlcCriticalRate world * time)) time := by
  let rate := rlcCriticalRate world
  have hlinear :
      HasDerivAt (fun t : ℝ => 1 + rate * t) rate time := by
    have h := (hasDerivAt_const time 1).add
      ((hasDerivAt_id time).const_mul rate)
    exact h.congr_deriv (by ring)
  have hinner :
      HasDerivAt (fun t : ℝ => -rate * t) (-rate) time := by
    have h := (hasDerivAt_id time).const_mul (-rate)
    exact h.congr_deriv (by ring)
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (-rate * t))
        (Real.exp (-rate * time) * (-rate)) time :=
    (Real.hasDerivAt_exp (-rate * time)).comp time hinner
  have hproduct := (hlinear.mul hexp).const_mul
    world.environment.initialVoltage
  have hfunction :=
    hproduct.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by
        change
          rlcCriticalState world t .storageVoltage =
            world.environment.initialVoltage *
              ((1 + rate * t) * Real.exp (-rate * t))
        simp only [rlcCriticalState, rate]
        ring)
  apply hfunction.congr_deriv
  dsimp only [rate]
  ring

theorem rlcCriticalCurrent_hasDerivAt (world : RLCWorld) (time : ℝ) :
    HasDerivAt
      (fun t => rlcCriticalState world t .inductorCurrent)
      (world.environment.initialVoltage *
        world.fabricated.capacitance *
        (rlcCriticalRate world) ^ 2 *
        (1 - rlcCriticalRate world * time) *
          Real.exp (-rlcCriticalRate world * time)) time := by
  let rate := rlcCriticalRate world
  have hinner :
      HasDerivAt (fun t : ℝ => -rate * t) (-rate) time := by
    have h := (hasDerivAt_id time).const_mul (-rate)
    exact h.congr_deriv (by ring)
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (-rate * t))
        (Real.exp (-rate * time) * (-rate)) time :=
    (Real.hasDerivAt_exp (-rate * time)).comp time hinner
  have hproduct := ((hasDerivAt_id time).mul hexp).const_mul
    (world.environment.initialVoltage *
      world.fabricated.capacitance * rate ^ 2)
  have hfunction :=
    hproduct.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by
        change
          rlcCriticalState world t .inductorCurrent =
            world.environment.initialVoltage *
              world.fabricated.capacitance * rate ^ 2 *
                (t * Real.exp (-rate * t))
        simp only [rlcCriticalState, rate]
        ring)
  apply hfunction.congr_deriv
  dsimp only [rate]
  simp only [id_eq]
  ring

theorem rlcCriticalLoad_hasDerivAt (world : RLCWorld) (time : ℝ) :
    HasDerivAt
      (fun t => rlcCriticalState world t .loadVoltage)
      (world.fabricated.resistance *
      (world.environment.initialVoltage *
        world.fabricated.capacitance *
        (rlcCriticalRate world) ^ 2 *
        (1 - rlcCriticalRate world * time) *
          Real.exp (-rlcCriticalRate world * time))) time := by
  have h :=
    (rlcCriticalCurrent_hasDerivAt world time).const_mul
      world.fabricated.resistance
  change HasDerivAt
    (fun t =>
      world.fabricated.resistance *
        (world.environment.initialVoltage *
          world.fabricated.capacitance *
          (rlcCriticalRate world) ^ 2 * t *
            Real.exp (-rlcCriticalRate world * t)))
    (world.fabricated.resistance *
      (world.environment.initialVoltage *
        world.fabricated.capacitance *
        (rlcCriticalRate world) ^ 2 *
        (1 - rlcCriticalRate world * time) *
          Real.exp (-rlcCriticalRate world * time))) time
  exact h

theorem rlcCritical_cap_ind_rate_sq
    {world : RLCWorld} (hadmissible : RLCAdmissible world)
    (hcritical : RLCCriticallyDamped world) :
    world.fabricated.capacitance *
      world.fabricated.inductance *
        (rlcCriticalRate world) ^ 2 = 1 := by
  unfold rlcCriticalRate RLCCriticallyDamped at *
  have hL : world.fabricated.inductance ≠ 0 :=
    ne_of_gt hadmissible.2.1
  field_simp [hL]
  nlinarith [hcritical]

theorem rlcCritical_res_cap_rate
    {world : RLCWorld} (hadmissible : RLCAdmissible world)
    (hcritical : RLCCriticallyDamped world) :
    world.fabricated.resistance *
      world.fabricated.capacitance *
        rlcCriticalRate world = 2 := by
  unfold rlcCriticalRate RLCCriticallyDamped at *
  have hL : world.fabricated.inductance ≠ 0 :=
    ne_of_gt hadmissible.2.1
  field_simp [hL]
  nlinarith [hcritical]

/-- The closed-form critical-damping trajectory is a genuine behavior. This
is the paired realizability theorem for the energy safety result. -/
theorem rlc_critical_realizable
    {world : RLCWorld}
    (hadmissible : RLCAdmissible world)
    (hcritical : RLCCriticallyDamped world)
    (hcurrent : world.environment.initialCurrent = 0) :
    RLCBehavior world (rlcCriticalBoundary world) () := by
  refine ⟨?_, ?_, hadmissible.2.2.2, ?_, ?_⟩
  · simp [rlcCriticalBoundary, rlcCriticalState]
  · simp [rlcCriticalBoundary, rlcCriticalState, hcurrent]
  · exact rlcCriticalState_absolutelyContinuous world
      world.environment.horizon
  · exact MeasureTheory.ae_restrict_of_forall_mem
      measurableSet_uIcc fun time _htime => by
      let derivative : VectorState RLCVariable :=
        fun index =>
          match index with
          | .storageVoltage =>
              -world.environment.initialVoltage *
                (rlcCriticalRate world) ^ 2 * time *
                  Real.exp (-rlcCriticalRate world * time)
          | .inductorCurrent =>
              world.environment.initialVoltage *
                world.fabricated.capacitance *
                (rlcCriticalRate world) ^ 2 *
                (1 - rlcCriticalRate world * time) *
                  Real.exp (-rlcCriticalRate world * time)
          | .loadVoltage =>
              world.fabricated.resistance *
                (world.environment.initialVoltage *
                  world.fabricated.capacitance *
                  (rlcCriticalRate world) ^ 2 *
                  (1 - rlcCriticalRate world * time) *
                    Real.exp (-rlcCriticalRate world * time))
      refine ⟨derivative, ?_, ?_⟩
      · intro index
        cases index with
        | storageVoltage =>
            exact rlcCriticalStorage_hasDerivAt world time
        | inductorCurrent =>
            exact rlcCriticalCurrent_hasDerivAt world time
        | loadVoltage =>
            exact rlcCriticalLoad_hasDerivAt world time
      · have hcli :=
          rlcCritical_cap_ind_rate_sq hadmissible hcritical
        have hcr :=
          rlcCritical_res_cap_rate hadmissible hcritical
        simp only [rlcDAE, rlcCriticalBoundary, rlcCriticalState, derivative]
        constructor
        · ring_nf
        constructor
        · linear_combination
            (world.environment.initialVoltage *
              Real.exp (-rlcCriticalRate world * time) *
              (1 - rlcCriticalRate world * time)) * hcli +
            (world.environment.initialVoltage *
              Real.exp (-rlcCriticalRate world * time) *
              rlcCriticalRate world * time) * hcr
        · ring

end LeanModels.Spice

namespace LeanModels.Circuit

def ElaboratedCircuit.toRLCNominal
    (circuit : ElaboratedCircuit)
    (capacitorName inductorName resistorName : String) :
    Except String LeanModels.Spice.RLCNominal := do
  let projected ← circuit.toDCCircuit.mapError fun error =>
    s!"RLC exact-DC projection failed: {repr error}"
  LeanModels.Spice.DCCircuit.toRLCNominal projected
    capacitorName inductorName resistorName

end LeanModels.Circuit
