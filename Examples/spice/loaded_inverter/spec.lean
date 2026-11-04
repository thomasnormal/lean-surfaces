import LeanModels.Python.Surface
import Examples.spice.loaded_inverter.proof

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
        loadCapacitance := 1 / 1000000000000 } := by proofs

theorem loaded_inverter_realizable :
    RealizableUnder LoadedInverterBehavior
      Examples.spice.loaded_inverter.proof.LoadedInverterExampleAllowed :=
  by proofs

theorem loaded_inverter_dc_realizable
    (world : LoadedInverterWorld)
    (hallowed :
      Examples.spice.loaded_inverter.proof.LoadedInverterExampleAllowed
        world) :
    ∃ output,
      LoadedInverterDC world.fabricated world.environment.supply
        world.environment.inputVoltage output := by proofs

theorem loaded_inverter_dae :
    SafeUnder LoadedInverterBehavior
      Examples.spice.loaded_inverter.proof.LoadedInverterExampleAllowed
      (fun world boundary _internal =>
        loadedInverterDAE.ACBehavesOn world world.environment.horizon
          boundary.outputVoltage) := by proofs

theorem loaded_inverter_no_overshoot :
    SafeUnder LoadedInverterBehavior
      Examples.spice.loaded_inverter.proof.LoadedInverterExampleAllowed
      (fun world boundary _internal =>
        NoOvershoot boundary.outputVoltage 0 world.environment.supply
          world.environment.horizon) := by proofs

theorem loaded_inverter_domain :
    StaysWithinValidityDomain LoadedInverterBehavior
      Examples.spice.loaded_inverter.proof.LoadedInverterExampleAllowed
      LoadedInverterValidityDomain := by proofs

theorem loaded_inverter_exponential_bound
    {world : LoadedInverterWorld} {boundary : LoadedInverterBoundary}
    (hallowed :
      Examples.spice.loaded_inverter.proof.LoadedInverterExampleAllowed
        world)
    (hbehavior : LoadedInverterBehavior world boundary ())
    {time : ℝ} (htime : time ∈ Icc 0 world.environment.horizon) :
    loadedInverterErrorTrace world boundary time ≤
      loadedInverterInitialError world *
        Real.exp (-loadedInverterDecayRate world * time) := by proofs

theorem loaded_inverter_settles_within
    {world : LoadedInverterWorld} {boundary : LoadedInverterBoundary}
    (hallowed :
      Examples.spice.loaded_inverter.proof.LoadedInverterExampleAllowed
        world)
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
      tolerance deadline world.environment.horizon := by proofs

/-- A11 INSTANTIATED: the settling deadline is DISCHARGED over the whole PVT
corner box, not assumed.  One microsecond settles to within 10 mV for every
allowed corner. -/
theorem loaded_inverter_settled_at_microsecond
    {world : LoadedInverterWorld} {boundary : LoadedInverterBoundary}
    (hallowed :
      Examples.spice.loaded_inverter.proof.LoadedInverterExampleAllowed
        world)
    (hbehavior : LoadedInverterBehavior world boundary ())
    (hhorizon : (1 / 1000000 : ℝ) ≤ world.environment.horizon) :
    SettlesWithin boundary.outputVoltage
      (if world.environment.input then 0 else world.environment.supply)
      (1 / 100) (1 / 1000000) world.environment.horizon := by proofs

theorem loaded_inverter_static_power_zero
    {world : LoadedInverterWorld}
    (hallowed :
      Examples.spice.loaded_inverter.proof.LoadedInverterExampleAllowed
        world)
    {output : ℝ}
    (hdc :
      LoadedInverterDC world.fabricated world.environment.supply
        world.environment.inputVoltage output) :
    loadedInverterSupplyCurrent world.fabricated world.environment.supply
      world.environment.inputVoltage output = 0 := by proofs

theorem loaded_inverter_assurance :
    AssuranceCase loadedInverter LoadedInverterBehavior
      Examples.spice.loaded_inverter.proof.LoadedInverterExampleAllowed
      Examples.spice.loaded_inverter.proof.loadedInverterSourceBinding
      (fun world boundary _internal =>
        NoOvershoot boundary.outputVoltage 0 world.environment.supply
          world.environment.horizon)
      LoadedInverterValidityDomain := by proofs

#assurance_report loadedInverter using loaded_inverter_assurance
  [loaded_inverter_dc_realizable, loaded_inverter_dae,
    loaded_inverter_exponential_bound, loaded_inverter_settles_within,
    loaded_inverter_static_power_zero]

#print axioms loaded_inverter_topology
#print axioms loaded_inverter_realizable
#print axioms loaded_inverter_dc_realizable
#print axioms loaded_inverter_dae
#print axioms loaded_inverter_no_overshoot
#print axioms loaded_inverter_domain
#print axioms loaded_inverter_exponential_bound
#print axioms loaded_inverter_settles_within
#print axioms loaded_inverter_static_power_zero
#print axioms loaded_inverter_assurance
#print axioms loaded_inverter_settled_at_microsecond
