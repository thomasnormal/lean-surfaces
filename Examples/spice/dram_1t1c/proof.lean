import LeanModels.Spice.Dram1T1C
import LeanModels.Circuit.Surface

namespace Examples.spice.dram_1t1c.proof

open LeanModels.Circuit LeanModels.Spice Set

load_circuit dram1T1C from
  "Examples/spice/dram_1t1c/dram_1t1c.cir"

theorem dram_1t1c_topology :
    dram1T1C.toDram1T1CNominal = .ok
      { storageNode := ⟨0⟩
        wordlineNode := ⟨2⟩
        bitlineNode := ⟨3⟩
        threshold := 1
        beta := 1 / 10000
        storageCapacitance := 3 / 100000000000000 } := by
  rfl

def dram1T1CNominal : Dram1T1CNominal :=
  match dram1T1C.toDram1T1CNominal with
  | .ok nominal => nominal
  | .error _ => default

theorem dram1T1CNominal_eq :
    dram1T1CNominal =
      { storageNode := ⟨0⟩
        wordlineNode := ⟨2⟩
        bitlineNode := ⟨3⟩
        threshold := 1
        beta := 1 / 10000
        storageCapacitance := 3 / 100000000000000 } := by
  unfold dram1T1CNominal
  rw [dram_1t1c_topology]

/-- The source deck fixes device parameters. Run controls and initial charge
remain universally quantified through the environment. -/
noncomputable def Dram1T1CExampleAllowed
    (world : Dram1T1CWorld) : Prop :=
  world.fabricated = dram1T1CNominal.instance ∧
    Dram1T1CAdmissible world

noncomputable def dram1T1CSourceBinding :
    SourceBinding dram1T1C Dram1T1CBehavior Dram1T1CExampleAllowed :=
  SourceBinding.checked LeanModels.Spice.ElaboratedCircuit.toDram1T1CNominal
    dram1T1C dram1T1CNominal
    (by
      change dram1T1C.toDram1T1CNominal = .ok dram1T1CNominal
      unfold dram1T1CNominal
      rw [dram_1t1c_topology])
    (fun _nominal => Dram1T1CBehavior)
    (fun nominal world =>
      world.fabricated = nominal.instance ∧ Dram1T1CAdmissible world)

theorem dram_1t1c_realizable :
    RealizableUnder Dram1T1CBehavior Dram1T1CExampleAllowed := by
  intro world hallowed
  exact dram1T1C_realizable world hallowed.2

theorem dram_1t1c_dae :
    SafeUnder Dram1T1CBehavior Dram1T1CExampleAllowed
      (fun world boundary _internal =>
        dram1T1CDAE.ACBehavesOn world world.environment.horizon
          boundary.storageVoltage) := by
  intro world boundary internal hallowed hbehavior
  exact dram1T1C_dae world boundary internal hallowed.2 hbehavior

theorem dram_1t1c_domain :
    StaysWithinValidityDomain Dram1T1CBehavior
      Dram1T1CExampleAllowed Dram1T1CValidityDomain := by
  intro world boundary internal hallowed hbehavior
  exact dram1T1C_stays_in_domain world boundary internal
    hallowed.2 hbehavior

/-- An unselected cell retains its exact initial stored voltage throughout
the requested finite horizon in the named zero-leakage MOS1 profile. -/
theorem dram_1t1c_hold_retention
    {world : Dram1T1CWorld} {boundary : Dram1T1CBoundary}
    (hallowed : Dram1T1CExampleAllowed world)
    (hmode : world.environment.mode = .hold)
    (hbehavior : Dram1T1CBehavior world boundary ()) :
    ∀ time ∈ Icc 0 world.environment.horizon,
      boundary.storageVoltage time =
        world.environment.initialVoltage := by
  exact dram1T1C_hold_retention hmode hbehavior

/-- In write-zero mode the DAE field is exactly the normalized MOS1 channel
current divided by the extracted storage capacitance. -/
theorem dram_1t1c_write_uses_mos1
    {world : Dram1T1CWorld}
    (hallowed : Dram1T1CExampleAllowed world)
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
  exact dram1T1C_writeField_eq_mos1 hallowed.2 hstorage0

theorem dram_1t1c_write_zero_settles
    {world : Dram1T1CWorld} {boundary : Dram1T1CBoundary}
    (hallowed : Dram1T1CExampleAllowed world)
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
  exact dram1T1C_write_zero_settles hallowed.2 hmode hbehavior
    htolerance hdeadline0 hdeadlineH hdeadline

theorem dram_1t1c_assurance :
    AssuranceCase dram1T1C Dram1T1CBehavior Dram1T1CExampleAllowed
      dram1T1CSourceBinding
      Dram1T1CValidityDomain Dram1T1CValidityDomain :=
  ⟨dram_1t1c_domain, dram_1t1c_realizable, dram_1t1c_domain⟩

end Examples.spice.dram_1t1c.proof
