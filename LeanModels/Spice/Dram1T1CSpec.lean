import LeanModels.Spice.Dram1T1C

/-!
# Properties of the open 1T1C model

This module imports the equation semantics and states its observation
properties. `Dram1T1C` does not import this module.
-/

namespace LeanModels.Spice

open LeanModels.Circuit Set

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
      intro time htime0 htimeH
      have hconstancy :
          ∀ time ∈ Icc 0 world.environment.horizon,
            boundary.storageVoltage time =
              world.environment.initialVoltage := by
        exact dram1T1C_hold_retention_from_dae hmode hbehavior
      rw [show boundary.storageVoltage time =
          world.environment.initialVoltage by
        exact hconstancy time ⟨htime0, htimeH⟩]
      exact ⟨hadmissible.2.2.2.2.1, hadmissible.2.2.2.2.2.1⟩
  | writeZero =>
      intro time htime0 htimeH
      have hloaded :
          LoadedInverterBehavior world.asLoadedInverter
            ⟨boundary.storageVoltage⟩ () := by
        simpa [Dram1T1CProgram, hmode] using hbehavior .evolution
      exact loadedInverter_no_overshoot hadmissible.asLoadedInverter
        hloaded.2 time ⟨htime0, htimeH⟩

theorem dram1T1C_hold_retention
    {world : Dram1T1CWorld} {boundary : Dram1T1CBoundary}
    (hmode : world.environment.mode = .hold)
    (hbehavior : Dram1T1CBehavior world boundary ()) :
    ∀ time ∈ Icc 0 world.environment.horizon,
      boundary.storageVoltage time = world.environment.initialVoltage := by
  exact dram1T1C_hold_retention_from_dae hmode hbehavior

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
    simpa [Dram1T1CProgram, hmode] using hbehavior .evolution
  have hsettles :=
    loadedInverter_settles_within hadmissible.asLoadedInverter hloaded.2
      htolerance hdeadline0 hdeadlineH
  apply hsettles
  simpa [loadedInverterInitialError, loadedInverterError,
    Dram1T1CWorld.asLoadedInverter, deterministicWorld] using hdeadline

end LeanModels.Spice
