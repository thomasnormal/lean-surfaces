import LeanModels.Spice.LoadedInverter
import LeanModels.Circuit.Surface

namespace Examples.spice.loaded_inverter.proof

open LeanModels.Circuit LeanModels.Spice Set

load_circuit loadedInverter from
  "Examples/spice/loaded_inverter/loaded_inverter.cir"

theorem loaded_inverter_topology :
    loadedInverter.toLoadedInverterNominal = .ok
      { inputNode := ⟨2⟩
        outputNode := ⟨0⟩
        supplyNode := ⟨3⟩
        nThreshold := 1
        pThreshold := 1
        nBeta := 1 / 10000
        pBeta := 1 / 20000
        loadCapacitance := 1 / 1000000000000 } := by
  rfl

/-- The checked adapter is the only path from the source deck to these
nominal parameters. -/
def loadedInverterNominal : LoadedInverterNominal :=
  match loadedInverter.toLoadedInverterNominal with
  | .ok nominal => nominal
  | .error _ => default

theorem loadedInverterNominal_eq :
    loadedInverterNominal =
      { inputNode := ⟨2⟩
        outputNode := ⟨0⟩
        supplyNode := ⟨3⟩
        nThreshold := 1
        pThreshold := 1
        nBeta := 1 / 10000
        pBeta := 1 / 20000
        loadCapacitance := 1 / 1000000000000 } := by
  unfold loadedInverterNominal
  rw [loaded_inverter_topology]

/-- Correlated fabrication corners and bounded run environments. -/
def LoadedInverterExampleAllowed : LoadedInverterWorld → Prop :=
  LoadedInverterCornerRun

/-- The source adapter fixes the supported MOS topology and nominal model
profile. `LoadedInverterCornerRun` is an explicit external PVT envelope around
that nominal projection; physical coverage of the envelope remains a separate
validity obligation in the assurance report. -/
def loadedInverterSourceBinding :
    SourceBinding loadedInverter LoadedInverterBehavior
      LoadedInverterExampleAllowed :=
  SourceBinding.checked
    LeanModels.Spice.ElaboratedCircuit.toLoadedInverterNominal
    loadedInverter loadedInverterNominal
    (by
      change loadedInverter.toLoadedInverterNominal =
        .ok loadedInverterNominal
      unfold loadedInverterNominal
      rw [loaded_inverter_topology])
    (fun _nominal => LoadedInverterBehavior)
    (fun _nominal => LoadedInverterCornerRun)

theorem loaded_inverter_realizable :
    RealizableUnder LoadedInverterBehavior
      LoadedInverterExampleAllowed := by
  intro world hallowed
  exact loadedInverter_realizable world
    (loadedInverterCornerRun_admissible hallowed)

/-- The source-backed nonlinear DC model has an operating point for every
corner and either rail input. -/
theorem loaded_inverter_dc_realizable
    (world : LoadedInverterWorld)
    (hallowed : LoadedInverterExampleAllowed world) :
    ∃ output,
      LoadedInverterDC world.fabricated world.environment.supply
        world.environment.inputVoltage output := by
  have hadmissible :=
    loadedInverterCornerRun_admissible hallowed
  have hsupply : 0 ≤ world.environment.supply := by
    linarith [hadmissible.2.2.2.1, hadmissible.2.2.2.2.1]
  apply loadedInverter_dc_exists world.fabricated
  · exact hsupply
  · cases hinput : world.environment.input <;>
      simp [LoadedInverterEnvironment.inputVoltage, hinput, hsupply]
  · cases hinput : world.environment.input <;>
      simp [LoadedInverterEnvironment.inputVoltage, hinput, hsupply]
  · exact hadmissible.1.le
  · exact hadmissible.2.1.le

/-- Every admitted trajectory is an absolutely-continuous solution of the
capacitor/MOS1 DAE almost everywhere. -/
theorem loaded_inverter_dae :
    SafeUnder LoadedInverterBehavior LoadedInverterExampleAllowed
      (fun world boundary _internal =>
        loadedInverterDAE.ACBehavesOn world world.environment.horizon
          boundary.outputVoltage) := by
  intro world boundary internal _hallowed hbehavior
  exact hbehavior.1.2

/-- Every solution remains between ground and its selected supply rail. -/
theorem loaded_inverter_no_overshoot :
    SafeUnder LoadedInverterBehavior LoadedInverterExampleAllowed
      (fun world boundary _internal =>
        NoOvershoot boundary.outputVoltage 0 world.environment.supply
          world.environment.horizon) := by
  intro world boundary _internal hallowed hbehavior
  have hdomain :=
    loadedInverter_no_overshoot
      (loadedInverterCornerRun_admissible hallowed) hbehavior.2
  intro time htime0 htimeH
  exact hdomain time ⟨htime0, htimeH⟩

theorem loaded_inverter_domain :
    StaysWithinValidityDomain LoadedInverterBehavior
      LoadedInverterExampleAllowed LoadedInverterValidityDomain := by
  intro world boundary _internal hallowed hbehavior
  exact loadedInverter_no_overshoot
    (loadedInverterCornerRun_admissible hallowed) hbehavior.2

/-- Quantitative PVT theorem: every admitted trajectory's error is bounded
by the instance-specific exponential envelope. -/
theorem loaded_inverter_exponential_bound
    {world : LoadedInverterWorld} {boundary : LoadedInverterBoundary}
    (hallowed : LoadedInverterExampleAllowed world)
    (hbehavior : LoadedInverterBehavior world boundary ())
    {time : ℝ} (htime : time ∈ Icc 0 world.environment.horizon) :
    loadedInverterErrorTrace world boundary time ≤
      loadedInverterInitialError world *
        Real.exp (-loadedInverterDecayRate world * time) := by
  exact loadedInverter_error_exponential_bound
    (loadedInverterCornerRun_admissible hallowed) hbehavior.2 htime

/-- A user-selected tolerance/deadline is discharged by comparing it with
the proved exponential envelope; no simulation trace enters the theorem. -/
theorem loaded_inverter_settles_within
    {world : LoadedInverterWorld} {boundary : LoadedInverterBoundary}
    (hallowed : LoadedInverterExampleAllowed world)
    (hbehavior : LoadedInverterBehavior world boundary ())
    {tolerance deadline : ℝ}
    (htolerance : 0 ≤ tolerance)
    (hdeadline0 : 0 ≤ deadline)
    (hdeadlineH : deadline ≤ world.environment.horizon)
    (hdeadline :
      loadedInverterInitialError world *
          Real.exp (-loadedInverterDecayRate world * deadline) ≤
        tolerance) :
    SettlesWithin boundary.outputVoltage
      (if world.environment.input then 0 else world.environment.supply)
      tolerance deadline world.environment.horizon := by
  exact LeanModels.Spice.loadedInverter_settles_within
    (loadedInverterCornerRun_admissible hallowed) hbehavior.2
      htolerance hdeadline0 hdeadlineH hdeadline

/-- Rail-valued DC states consume zero static channel power in this named
MOS1 profile. -/
theorem loaded_inverter_static_power_zero
    {world : LoadedInverterWorld}
    (hallowed : LoadedInverterExampleAllowed world)
    {output : ℝ}
    (hdc :
      LoadedInverterDC world.fabricated world.environment.supply
        world.environment.inputVoltage output) :
    loadedInverterSupplyCurrent world.fabricated world.environment.supply
      world.environment.inputVoltage output = 0 := by
  have hadmissible :=
    loadedInverterCornerRun_admissible hallowed
  rcases hadmissible with
    ⟨hnbeta, hpbeta, _hcap, hnt0, hnt, hpt0, hpt,
      _hinitial0, _hinitial1, _hhorizon⟩
  have hsupply : 0 < world.environment.supply := by
    linarith
  simpa [LoadedInverterEnvironment.inputVoltage] using
    (LeanModels.Spice.loadedInverter_static_power_zero
      (input := world.environment.input)
      (output := output)
      hsupply
      hnt0 hnt hpt0 hpt hnbeta hpbeta hdc)

theorem loaded_inverter_assurance :
    AssuranceCase loadedInverter LoadedInverterBehavior
      LoadedInverterExampleAllowed
      loadedInverterSourceBinding
      (fun world boundary _internal =>
        NoOvershoot boundary.outputVoltage 0 world.environment.supply
          world.environment.horizon)
      LoadedInverterValidityDomain :=
  ⟨loaded_inverter_no_overshoot, loaded_inverter_realizable,
    loaded_inverter_domain⟩

end Examples.spice.loaded_inverter.proof
