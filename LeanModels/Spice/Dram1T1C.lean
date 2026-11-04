import LeanModels.Spice.LoadedInverter
import LeanModels.Circuit.Equation

/-!
# Thin open 1T1C DRAM cell

This first DRAM slice proves hold retention and write-zero for an open cell
containing one NMOS access device and one storage capacitor. Wordline and
bitline drivers are run-world inputs, not fixed testbench sources in the
component deck.

Write-zero is exactly the rail-driven NMOS discharge already verified for the
loaded inverter. Hold uses an ideal zero-leakage DAE field; exact constancy is
derived from that evolution law and the initial condition rather than asserted
as a behavior clause. In the nonnegative rail domain, a theorem identifies
that zero field with the KCL field of the bidirectional MOS1 access device
held below threshold. Write-one threshold loss, destructive read/charge
sharing, leakage, and sense-amplifier interaction are intentionally deferred
to the full DRAM slice.
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

inductive Dram1T1CClause where
  | initialCondition
  | evolution
deriving Repr, DecidableEq

/-- The open-cell behavior contains only its initial condition and physical
DAE evolution. Hold constancy is derived below, not stored as a clause. -/
noncomputable def Dram1T1CProgram :
    EquationProgram Dram1T1CClause Dram1T1CWorld Dram1T1CBoundary Unit where
  origin
    | .initialCondition => .initialCondition "storage capacitor voltage"
    | .evolution => .evolution "1T1C hold/write DAE"
  equation clause world boundary _internal :=
    match clause, world.environment.mode with
    | .initialCondition, .hold =>
        boundary.storageVoltage 0 = world.environment.initialVoltage
    | .initialCondition, .writeZero => True
    | .evolution, .hold =>
        dram1T1CDAE.ACBehavesOn world world.environment.horizon
          boundary.storageVoltage
    | .evolution, .writeZero =>
        LoadedInverterBehavior world.asLoadedInverter
          ⟨boundary.storageVoltage⟩ ()

/-- Public behavior: hold is a physical constant-charge DAE trace; write-zero
uses the charge-consistent loaded-MOS DAE. -/
noncomputable def Dram1T1CBehavior :
    Behavior Dram1T1CWorld Dram1T1CBoundary Unit :=
  Dram1T1CProgram.behavior

theorem dram1T1CEquationManifest :
    EquationManifest Dram1T1CProgram [] := by
  constructor
  · simp
  · intro contract hcontract
    rcases hcontract with ⟨clause, hclause⟩
    cases clause <;>
      simp [Dram1T1CProgram] at hclause ⊢

theorem dram1T1CProgram_physicsOnly :
    Dram1T1CProgram.PhysicsOnly := by
  intro clause
  cases clause <;> rfl

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

/-- Inside the nonnegative rail domain, the ideal zero-leakage hold field is
exactly the storage-capacitor KCL field obtained from the bidirectional MOS1
access device with its wordline held low. -/
theorem dram1T1C_holdField_eq_mos1
    {world : Dram1T1CWorld}
    (hadmissible : Dram1T1CAdmissible world)
    (hmode : world.environment.mode = .hold)
    {storage bitline : ℝ}
    (hstorage : 0 ≤ storage)
    (hbitline : 0 ≤ bitline) :
    dram1T1CField world storage =
      -(mos1TerminalCurrent
          { polarity := .nmos
            threshold := world.fabricated.threshold
            beta := world.fabricated.beta
            lambda := 0 }
          0 storage bitline) /
        world.fabricated.storageCapacitance := by
  have hcurrent :
      mos1TerminalCurrent
          { polarity := .nmos
            threshold := world.fabricated.threshold
            beta := world.fabricated.beta
            lambda := 0 }
          0 storage bitline = 0 := by
    apply mos1TerminalCurrent_nmos_eq_zero_of_cutoff
    · linarith [hadmissible.2.2.1]
    · linarith [hadmissible.2.2.1]
  simp [dram1T1CField, hmode, hcurrent]

/-- The constant trace realizes the zero-field hold DAE on every nonnegative
horizon. -/
theorem dram1T1C_hold_dae_realizable
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

/-- In hold mode, the DAE residual forces zero derivative. Absolute
continuity and the initial-condition clause therefore derive exact retention
throughout the requested horizon. -/
theorem dram1T1C_hold_retention_from_dae
    {world : Dram1T1CWorld} {boundary : Dram1T1CBoundary}
    (hmode : world.environment.mode = .hold)
    (hbehavior : Dram1T1CBehavior world boundary ()) :
    ∀ time ∈ Icc 0 world.environment.horizon,
      boundary.storageVoltage time =
        world.environment.initialVoltage := by
  have hinitial :
      boundary.storageVoltage 0 = world.environment.initialVoltage := by
    simpa [Dram1T1CBehavior, Dram1T1CProgram, hmode] using
      hbehavior .initialCondition
  have hevolution :
      dram1T1CDAE.ACBehavesOn world world.environment.horizon
        boundary.storageVoltage := by
    simpa [Dram1T1CBehavior, Dram1T1CProgram, hmode] using
      hbehavior .evolution
  have hconstant :=
    dram1T1CDAE.constant_on_of_residual_forces_zero hevolution
      (fun _time _storage derivative hresidual => by
        simpa [dram1T1CDAE, dram1T1CField, hmode] using hresidual)
  intro time htime
  exact (hconstant time htime).trans hinitial

theorem dram1T1C_realizable :
    RealizableUnder Dram1T1CBehavior Dram1T1CAdmissible := by
  intro world hadmissible
  cases hmode : world.environment.mode with
  | hold =>
      refine ⟨⟨fun _time => world.environment.initialVoltage⟩, (), ?_⟩
      intro clause
      cases clause
      case initialCondition =>
        simp [Dram1T1CProgram, hmode]
      case evolution =>
        simpa [Dram1T1CProgram, hmode] using
          dram1T1C_hold_dae_realizable hmode hadmissible.2.2.2.2.2.2
  | writeZero =>
      obtain ⟨boundary, internal, hbehavior⟩ :=
        loadedInverter_realizable world.asLoadedInverter
          hadmissible.asLoadedInverter
      refine ⟨⟨boundary.outputVoltage⟩, internal, ?_⟩
      intro clause
      cases clause
      case initialCondition =>
        simp [Dram1T1CProgram, hmode]
      case evolution =>
        simpa [Dram1T1CProgram, hmode] using hbehavior

theorem dram1T1C_dae :
    SafeUnder Dram1T1CBehavior Dram1T1CAdmissible
      (fun world boundary _internal =>
        dram1T1CDAE.ACBehavesOn world world.environment.horizon
          boundary.storageVoltage) := by
  intro world boundary _internal _hadmissible hbehavior
  cases hmode : world.environment.mode with
  | hold =>
      simpa [Dram1T1CProgram, hmode] using hbehavior .evolution
  | writeZero =>
      have hloaded :
          LoadedInverterBehavior world.asLoadedInverter
            ⟨boundary.storageVoltage⟩ () := by
        simpa [Dram1T1CProgram, hmode] using hbehavior .evolution
      have hphysical := hloaded.1.2
      simpa [ScalarDAE.ACBehavesOn, dram1T1CDAE,
        loadedInverterDAE, dram1T1CField, hmode,
        Dram1T1CWorld.asLoadedInverter, deterministicWorld] using hphysical

end LeanModels.Spice

namespace LeanModels.Circuit

def ElaboratedCircuit.toDram1T1CNominal
    (circuit : ElaboratedCircuit) :
    Except String LeanModels.Spice.Dram1T1CNominal :=
  LeanModels.Spice.ElaboratedCircuit.toDram1T1CNominal circuit

end LeanModels.Circuit
