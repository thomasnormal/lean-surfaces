import LeanModels.Spice.LoadedInverter

/-!
# Thin open 1T1C DRAM cell

This first DRAM slice proves hold retention and write-zero for an open cell
containing one NMOS access device and one storage capacitor. Wordline and
bitline drivers are run-world inputs, not fixed testbench sources in the
component deck.

Write-zero is exactly the rail-driven NMOS discharge already verified for the
loaded inverter. Hold uses MOS1 cutoff and zero leakage, so stored charge is
constant. Write-one threshold loss, destructive read/charge sharing, leakage,
and sense-amplifier interaction are intentionally deferred to the full DRAM
slice.
-/

namespace LeanModels.Spice

open LeanModels.Circuit Set MeasureTheory

inductive Dram1T1CMode
  | hold
  | writeZero
deriving Repr, DecidableEq, BEq, Inhabited

structure Dram1T1CInstance where
  threshold : ℝ
  beta : ℝ
  storageCapacitance : ℝ

structure Dram1T1CEnvironment where
  supply : ℝ
  mode : Dram1T1CMode
  initialVoltage : ℝ
  horizon : ℝ

abbrev Dram1T1CWorld :=
  RunWorld Dram1T1CInstance Dram1T1CEnvironment Unit Unit

structure Dram1T1CBoundary where
  storageVoltage : DenseTrace ℝ

def Dram1T1CAdmissible (world : Dram1T1CWorld) : Prop :=
  0 < world.fabricated.beta ∧
  0 < world.fabricated.storageCapacitance ∧
  0 < world.fabricated.threshold ∧
  world.fabricated.threshold < world.environment.supply ∧
  0 ≤ world.environment.initialVoltage ∧
  world.environment.initialVoltage ≤ world.environment.supply ∧
  0 ≤ world.environment.horizon

/-- Exact source data recovered from the typed one-transistor/one-capacitor
deck. -/
structure Dram1T1CNominal where
  storageNode : LeanModels.Circuit.NodeId
  wordlineNode : LeanModels.Circuit.NodeId
  bitlineNode : LeanModels.Circuit.NodeId
  threshold : Rat
  beta : Rat
  storageCapacitance : Rat
deriving Repr, BEq, Inhabited

def ElaboratedCircuit.toDram1T1CNominal
    (circuit : ElaboratedCircuit) : Except String Dram1T1CNominal := do
  if circuit.devices.size != 2 then
    throw s!"1T1C cell requires exactly two devices, found {circuit.devices.size}"
  let mosfets := circuit.devices.toList.filterMap fun
    | .mosfet _ drain gate source bulk model =>
        some (drain, gate, source, bulk, model)
    | _ => none
  let capacitors := circuit.devices.toList.filterMap fun
    | .capacitor _ positive negative value =>
        some (positive, negative, value)
    | _ => none
  let (storage, wordline, bitline, bulk, modelId) ←
    match mosfets with
    | [mosfet] => pure mosfet
    | _ => throw "1T1C cell requires exactly one MOSFET"
  let (capStorage, capGround, capacitance) ←
    match capacitors with
    | [capacitor] => pure capacitor
    | _ => throw "1T1C cell requires exactly one storage capacitor"
  unless bulk == circuit.ground && capStorage == storage &&
      capGround == circuit.ground do
    throw "1T1C storage/bulk connectivity does not match the proved topology"
  let model ← match circuit.models[modelId.index]? with
    | some (.mos1 model) => pure model
    | _ => throw "1T1C access model is missing or unsupported"
  unless model.polarity == .nmos &&
      model.channelLengthModulation == 0 &&
      model.junctionSaturation == 0 do
    throw "1T1C cell requires the named NMOS LAMBDA=0, IS=0 profile"
  pure
    { storageNode := storage
      wordlineNode := wordline
      bitlineNode := bitline
      threshold := model.threshold
      beta := model.transconductance
      storageCapacitance := capacitance }

noncomputable def Dram1T1CNominal.instance
    (nominal : Dram1T1CNominal) : Dram1T1CInstance :=
  { threshold := nominal.threshold
    beta := nominal.beta
    storageCapacitance := nominal.storageCapacitance }

noncomputable def Dram1T1CWorld.asLoadedInverter
    (world : Dram1T1CWorld) : LoadedInverterWorld :=
  deterministicWorld
    { nThreshold := world.fabricated.threshold
      pThreshold := world.fabricated.threshold
      nBeta := world.fabricated.beta
      pBeta := world.fabricated.beta
      loadCapacitance := world.fabricated.storageCapacitance }
    { supply := world.environment.supply
      input := true
      initialVoltage := world.environment.initialVoltage
      horizon := world.environment.horizon }

theorem Dram1T1CAdmissible.asLoadedInverter
    {world : Dram1T1CWorld} (hadmissible : Dram1T1CAdmissible world) :
    LoadedInverterAdmissible world.asLoadedInverter := by
  rcases hadmissible with
    ⟨hbeta, hcap, hthreshold0, hthreshold1, hinitial0,
      hinitial1, hhorizon⟩
  exact ⟨hbeta, hbeta, hcap, hthreshold0, hthreshold1,
    hthreshold0, hthreshold1, hinitial0, hinitial1, hhorizon⟩

/-- The charge on the storage plate; the ground plate carries its negative. -/
noncomputable def dram1T1CStoredCharge
    (world : Dram1T1CWorld) (voltage : ℝ) : ℝ :=
  world.fabricated.storageCapacitance * voltage

theorem dram1T1C_charge_conservative
    (world : Dram1T1CWorld) (voltage : ℝ) :
    dram1T1CStoredCharge world voltage +
      (-dram1T1CStoredCharge world voltage) = 0 := by
  ring

noncomputable def dram1T1CField
    (world : Dram1T1CWorld) (storage : ℝ) : ℝ :=
  match world.environment.mode with
  | .hold => 0
  | .writeZero =>
      loadedInverterField world.asLoadedInverter storage

noncomputable def dram1T1CDAE : ScalarDAE Dram1T1CWorld where
  residual world _time storage derivative :=
    derivative = dram1T1CField world storage

/-- Public behavior: hold is a physical constant-charge DAE trace; write-zero
uses the charge-consistent loaded-MOS DAE. -/
noncomputable def Dram1T1CBehavior :
    Behavior Dram1T1CWorld Dram1T1CBoundary Unit :=
  fun world boundary _internal =>
    match world.environment.mode with
    | .hold =>
        boundary.storageVoltage 0 = world.environment.initialVoltage ∧
        dram1T1CDAE.ACBehavesOn world world.environment.horizon
          boundary.storageVoltage ∧
        ∀ time ∈ Icc 0 world.environment.horizon,
          boundary.storageVoltage time =
            world.environment.initialVoltage
    | .writeZero =>
        LoadedInverterBehavior world.asLoadedInverter
          ⟨boundary.storageVoltage⟩ ()

theorem dram1T1C_writeField_eq_mos1
    {world : Dram1T1CWorld} (hadmissible : Dram1T1CAdmissible world)
    {storage : ℝ} (hstorage0 : 0 ≤ storage) :
    dram1T1CField
        { world with environment := { world.environment with
            mode := .writeZero } } storage =
      -(mos1ForwardCurrent
          { polarity := .nmos
            threshold := world.fabricated.threshold
            beta := world.fabricated.beta
            lambda := 0 }
          world.environment.supply storage) /
        world.fabricated.storageCapacitance := by
  rcases hadmissible with
    ⟨hbeta, hcap, hthreshold0, hthreshold1, hinitial0,
      hinitial1, hhorizon⟩
  simp only [dram1T1CField, Dram1T1CWorld.asLoadedInverter,
    loadedInverterField, loadedInverterNOverdrive, deterministicWorld,
    if_true]
  rw [railCurrent_eq_mos1 hbeta.le hthreshold1.le hstorage0]

private theorem dram1T1C_hold_physical
    {world : Dram1T1CWorld}
    (hmode : world.environment.mode = .hold)
    (hhorizon : 0 ≤ world.environment.horizon) :
    dram1T1CDAE.ACBehavesOn world world.environment.horizon
      (fun _time => world.environment.initialVoltage) := by
  refine ⟨hhorizon, ?_, ?_⟩
  · exact (LipschitzWith.const world.environment.initialVoltage).lipschitzOnWith
      |>.absolutelyContinuousOnInterval
  · exact MeasureTheory.ae_restrict_of_forall_mem
      measurableSet_uIcc fun time _htime => by
        refine ⟨0, hasDerivAt_const time _, ?_⟩
        simp [dram1T1CDAE, dram1T1CField, hmode]

theorem dram1T1C_realizable :
    RealizableUnder Dram1T1CBehavior Dram1T1CAdmissible := by
  intro world hadmissible
  cases hmode : world.environment.mode with
  | hold =>
      refine ⟨⟨fun _time => world.environment.initialVoltage⟩, (), ?_⟩
      rw [Dram1T1CBehavior, hmode]
      exact ⟨rfl, dram1T1C_hold_physical hmode hadmissible.2.2.2.2.2.2,
        fun _time _htime => rfl⟩
  | writeZero =>
      obtain ⟨boundary, internal, hbehavior⟩ :=
        loadedInverter_realizable world.asLoadedInverter
          hadmissible.asLoadedInverter
      exact ⟨⟨boundary.outputVoltage⟩, internal, by
        simpa [Dram1T1CBehavior, hmode] using hbehavior⟩

theorem dram1T1C_dae :
    SafeUnder Dram1T1CBehavior Dram1T1CAdmissible
      (fun world boundary _internal =>
        dram1T1CDAE.ACBehavesOn world world.environment.horizon
          boundary.storageVoltage) := by
  intro world boundary _internal _hadmissible hbehavior
  cases hmode : world.environment.mode with
  | hold =>
      rw [Dram1T1CBehavior, hmode] at hbehavior
      exact hbehavior.2.1
  | writeZero =>
      rw [Dram1T1CBehavior, hmode] at hbehavior
      have hphysical := hbehavior.1.2
      simpa [ScalarDAE.ACBehavesOn, dram1T1CDAE,
        loadedInverterDAE, dram1T1CField, hmode,
        Dram1T1CWorld.asLoadedInverter, deterministicWorld] using hphysical

def Dram1T1CValidityDomain
    (world : Dram1T1CWorld) (boundary : Dram1T1CBoundary)
    (_internal : Unit) : Prop :=
  NoOvershoot boundary.storageVoltage 0 world.environment.supply
    world.environment.horizon

theorem dram1T1C_stays_in_domain :
    StaysWithinValidityDomain Dram1T1CBehavior Dram1T1CAdmissible
      Dram1T1CValidityDomain := by
  intro world boundary _internal hadmissible hbehavior
  cases hmode : world.environment.mode with
  | hold =>
      rw [Dram1T1CBehavior, hmode] at hbehavior
      intro time htime0 htimeH
      rw [hbehavior.2.2 time ⟨htime0, htimeH⟩]
      exact ⟨hadmissible.2.2.2.2.1, hadmissible.2.2.2.2.2.1⟩
  | writeZero =>
      rw [Dram1T1CBehavior, hmode] at hbehavior
      intro time htime0 htimeH
      exact loadedInverter_no_overshoot hadmissible.asLoadedInverter
        hbehavior.2 time ⟨htime0, htimeH⟩

theorem dram1T1C_hold_retention
    {world : Dram1T1CWorld} {boundary : Dram1T1CBoundary}
    (hmode : world.environment.mode = .hold)
    (hbehavior : Dram1T1CBehavior world boundary ()) :
    ∀ time ∈ Icc 0 world.environment.horizon,
      boundary.storageVoltage time = world.environment.initialVoltage := by
  rw [Dram1T1CBehavior, hmode] at hbehavior
  exact hbehavior.2.2

theorem dram1T1C_write_zero_settles
    {world : Dram1T1CWorld} {boundary : Dram1T1CBoundary}
    (hadmissible : Dram1T1CAdmissible world)
    (hmode : world.environment.mode = .writeZero)
    (hbehavior : Dram1T1CBehavior world boundary ())
    {tolerance deadline : ℝ}
    (htolerance : 0 ≤ tolerance)
    (hdeadline0 : 0 ≤ deadline)
    (hdeadlineH : deadline ≤ world.environment.horizon)
    (hdeadline :
      world.environment.initialVoltage *
          Real.exp
            (-loadedInverterDecayRate world.asLoadedInverter * deadline) ≤
        tolerance) :
    SettlesWithin boundary.storageVoltage 0 tolerance deadline
      world.environment.horizon := by
  have hloaded :
      LoadedInverterBehavior world.asLoadedInverter
        ⟨boundary.storageVoltage⟩ () := by
    simpa [Dram1T1CBehavior, hmode] using hbehavior
  have hsettles :=
    loadedInverter_settles_within hadmissible.asLoadedInverter hloaded.2
      htolerance hdeadline0 hdeadlineH
  apply hsettles
  simpa [loadedInverterInitialError, loadedInverterError,
    Dram1T1CWorld.asLoadedInverter, deterministicWorld] using hdeadline

end LeanModels.Spice

namespace LeanModels.Circuit

def ElaboratedCircuit.toDram1T1CNominal
    (circuit : ElaboratedCircuit) :
    Except String LeanModels.Spice.Dram1T1CNominal :=
  LeanModels.Spice.ElaboratedCircuit.toDram1T1CNominal circuit

end LeanModels.Circuit
