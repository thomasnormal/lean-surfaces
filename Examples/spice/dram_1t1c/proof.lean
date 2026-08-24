import LeanModels.Spice.Dram1T1C
import LeanModels.Spice.Dram1T1CSpec
import LeanModels.Spice.DramWriteSpec
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

noncomputable def dram1T1CWriteInstance : DramWriteInstance :=
  dram1T1CNominal.instance.asDramWriteInstance

theorem dram_1t1c_write_instance_from_source :
    dram1T1CWriteInstance =
      { threshold := 1
        beta := 1 / 10000
        storageCapacitance := 3 / 100000000000000 } := by
  simp [dram1T1CWriteInstance, dram1T1CNominal_eq,
    Dram1T1CNominal.instance, Dram1T1CInstance.asDramWriteInstance]

noncomputable def dram1T1CWriteOneWorld
    (initialStorage horizon : ℝ) : DramWriteWorld :=
  deterministicWorld dram1T1CWriteInstance
    { wordlineVoltage := 5
      bitlineVoltage := 5
      initialStorage
      horizon }

noncomputable def dram1T1CWriteOneAllowedOf
    (nominal : Dram1T1CNominal) (world : DramWriteWorld) : Prop :=
  ∃ initialStorage horizon,
    world =
      deterministicWorld nominal.instance.asDramWriteInstance
        { wordlineVoltage := 5
          bitlineVoltage := 5
          initialStorage
          horizon } ∧
      0 ≤ initialStorage ∧ initialStorage ≤ 4 ∧
      (1 / 1000000000 : ℝ) ≤ horizon

noncomputable def Dram1T1CWriteOneAllowed : DramWriteWorld → Prop :=
  dram1T1CWriteOneAllowedOf dram1T1CNominal

theorem dram_1t1c_write_one_world_from_source
    (initialStorage horizon : ℝ) :
    dram1T1CWriteOneWorld initialStorage horizon =
      nominalDramWriteOneWorld initialStorage horizon := by
  rw [dram1T1CWriteOneWorld, nominalDramWriteOneWorld,
    dram_1t1c_write_instance_from_source]

theorem dram_1t1c_equation_manifest :
    EquationManifest Dram1T1CProgram [] :=
  dram1T1CEquationManifest

theorem dram_1t1c_physics_only :
    Dram1T1CProgram.PhysicsOnly :=
  dram1T1CProgram_physicsOnly

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

/-- The hold field agrees with the primitive bidirectional MOS1/capacitor KCL
inside the proved nonnegative voltage domain. -/
theorem dram_1t1c_hold_uses_mos1
    {world : Dram1T1CWorld}
    (hallowed : Dram1T1CExampleAllowed world)
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
  exact dram1T1C_holdField_eq_mos1 hallowed.2 hmode hstorage hbitline

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

/-- A12: at the pinned nominal instance and a 5 V supply, the write-zero decay
rate is exactly `16000000000/3` per second.  The deck's world pins `fabricated`
but leaves `supply` free above the threshold, so the rate has NO uniform lower
bound over the allowed set -- pinning the supply is what makes it a constant. -/
theorem dram_1t1c_nominal_decayRate {world : Dram1T1CWorld}
    (hallowed : Dram1T1CExampleAllowed world)
    (hsupply : world.environment.supply = 5) :
    loadedInverterDecayRate world.asLoadedInverter = 16000000000 / 3 := by
  obtain ⟨hfab, hadm⟩ := hallowed
  unfold Dram1T1CWorld.asLoadedInverter loadedInverterDecayRate
    loadedInverterNOverdrive
  simp only [deterministicWorld, hfab, dram1T1CNominal_eq,
    Dram1T1CNominal.instance, hsupply]
  norm_num

/-- A12 INSTANTIATED.  `dram_1t1c_write_zero_settles` carried its deadline as a
HYPOTHESIS.  At the nominal instance and 5 V, two nanoseconds settle the storage
node to within 10 mV, certified at split depth 8.

The rate times ONE nanosecond is exactly `16/3` -- the same constant
`DramBankCoreSpec.lean` proved by hand before the F2 kit existed.  Two
nanoseconds gives `32/3`, and `5 * (3/7)^8 = 32805/5764801`, comfortably under
`1/100`. -/
theorem dram_1t1c_write_zero_settled_at_2ns
    {world : Dram1T1CWorld} {boundary : Dram1T1CBoundary}
    (hallowed : Dram1T1CExampleAllowed world)
    (hmode : world.environment.mode = .writeZero)
    (hbehavior : Dram1T1CBehavior world boundary ())
    (hsupply : world.environment.supply = 5)
    (hhorizon : (1 / 500000000 : ℝ) ≤ world.environment.horizon) :
    SettlesWithin boundary.storageVoltage 0 (1 / 100) (1 / 500000000)
      world.environment.horizon := by
  refine dram_1t1c_write_zero_settles hallowed hmode hbehavior
    (by norm_num) (by norm_num) hhorizon ?_
  have hinit0 : 0 ≤ world.environment.initialVoltage :=
    hallowed.2.2.2.2.2.1
  have hinit1 : world.environment.initialVoltage ≤ 5 := by
    rw [← hsupply]; exact hallowed.2.2.2.2.2.2.1
  have hval : (-(16000000000 / 3 : ℝ)) * (1 / 500000000) = -(32 / 3) := by
    norm_num
  rw [dram_1t1c_nominal_decayRate hallowed hsupply, hval]
  have hexp : Real.exp (-(32 / 3 : ℝ)) ≤ (3 / 7) ^ 8 :=
    LeanModels.Circuit.exp_neg_le_of_pow_le (by norm_num) 8 (by norm_num)
      (by norm_num)
  have hexp0 : (0:ℝ) ≤ Real.exp (-(32 / 3 : ℝ)) := (Real.exp_pos _).le
  nlinarith

theorem dram_1t1c_write_one_equation_manifest :
    EquationManifest DramWriteProgram [] :=
  dramWriteEquationManifest

theorem dram_1t1c_write_one_physics_only :
    DramWriteProgram.PhysicsOnly :=
  dramWriteProgram_physicsOnly

/-- Every source-backed nominal write-one trajectory starting from zero
enters the `[3 V, 4 V]` band within one nanosecond. -/
theorem dram_1t1c_write_one_settles
    {horizon : ℝ} {boundary : DramWriteBoundary}
    (hdeadline : (1 / 1000000000 : ℝ) ≤ horizon)
    (hbehavior :
      DramWriteBehavior (dram1T1CWriteOneWorld 0 horizon) boundary ()) :
    DramWriteOneNanosecondSpecification
      (dram1T1CWriteOneWorld 0 horizon) boundary () := by
  rw [dram_1t1c_write_one_world_from_source] at hbehavior ⊢
  exact nominalDramWriteOne_zero_to_high_by_one_ns hdeadline hbehavior

/-- The same source-backed write guarantee is inhabited, ruling out vacuous
universal correctness. -/
theorem dram_1t1c_write_one_realizable
    {horizon : ℝ} (hdeadline : (1 / 1000000000 : ℝ) ≤ horizon) :
    ∃ boundary,
      DramWriteBehavior
          (dram1T1CWriteOneWorld 0 horizon) boundary () ∧
        DramWriteOneNanosecondSpecification
          (dram1T1CWriteOneWorld 0 horizon) boundary () := by
  rw [dram_1t1c_write_one_world_from_source]
  exact
    nominalDramWriteOne_zero_to_high_by_one_ns_realizable hdeadline

noncomputable def dram1T1CWriteOneSourceBinding :
    SourceBinding dram1T1C DramWriteBehavior Dram1T1CWriteOneAllowed :=
  SourceBinding.checked LeanModels.Spice.ElaboratedCircuit.toDram1T1CNominal
    dram1T1C dram1T1CNominal
    (by
      change dram1T1C.toDram1T1CNominal = .ok dram1T1CNominal
      unfold dram1T1CNominal
      rw [dram_1t1c_topology])
    (fun _nominal => DramWriteBehavior)
    dram1T1CWriteOneAllowedOf

theorem dram_1t1c_write_one_safe :
    SafeUnder DramWriteBehavior Dram1T1CWriteOneAllowed
      DramWriteOneNanosecondSpecification := by
  intro world boundary _internal hallowed hbehavior
  rcases hallowed with
    ⟨initialStorage, horizon, hworld, hinitial0, hinitial4, hdeadline⟩
  subst world
  have hworldSource :
      deterministicWorld dram1T1CNominal.instance.asDramWriteInstance
          { wordlineVoltage := 5
            bitlineVoltage := 5
            initialStorage
            horizon } =
        nominalDramWriteOneWorld initialStorage horizon := by
    change dram1T1CWriteOneWorld initialStorage horizon =
      nominalDramWriteOneWorld initialStorage horizon
    exact dram_1t1c_write_one_world_from_source initialStorage horizon
  rw [hworldSource] at hbehavior ⊢
  apply nominalDramWriteOne_settles_within
    hinitial4 (by linarith) hbehavior
  · norm_num
  · norm_num
  · exact hdeadline
  · have hdenominator :=
      nominalDramWriteOneTrace_denominator_pos
        hinitial4 (show (0 : ℝ) ≤ 1 / 1000000000 by norm_num)
    rw [div_le_iff₀ hdenominator]
    norm_num [nominalDramWriteOneRate]
    linarith

theorem dram_1t1c_write_one_realizable_all :
    RealizableUnder DramWriteBehavior Dram1T1CWriteOneAllowed := by
  intro world hallowed
  rcases hallowed with
    ⟨initialStorage, horizon, hworld, _hinitial0, hinitial4, hdeadline⟩
  subst world
  have hworldSource :
      deterministicWorld dram1T1CNominal.instance.asDramWriteInstance
          { wordlineVoltage := 5
            bitlineVoltage := 5
            initialStorage
            horizon } =
        nominalDramWriteOneWorld initialStorage horizon := by
    change dram1T1CWriteOneWorld initialStorage horizon =
      nominalDramWriteOneWorld initialStorage horizon
    exact dram_1t1c_write_one_world_from_source initialStorage horizon
  rw [hworldSource]
  obtain ⟨boundary, hbehavior⟩ :=
    nominalDramWriteOne_realizable hinitial4 (by linarith)
  exact ⟨boundary, (), hbehavior⟩

theorem dram_1t1c_write_one_domain :
    StaysWithinValidityDomain DramWriteBehavior
      Dram1T1CWriteOneAllowed DramWriteRailDomain := by
  intro world boundary _internal hallowed hbehavior
  rcases hallowed with
    ⟨initialStorage, horizon, hworld, hinitial0, hinitial4, hdeadline⟩
  subst world
  have hworldSource :
      deterministicWorld dram1T1CNominal.instance.asDramWriteInstance
          { wordlineVoltage := 5
            bitlineVoltage := 5
            initialStorage
            horizon } =
        nominalDramWriteOneWorld initialStorage horizon := by
    change dram1T1CWriteOneWorld initialStorage horizon =
      nominalDramWriteOneWorld initialStorage horizon
    exact dram_1t1c_write_one_world_from_source initialStorage horizon
  rw [hworldSource] at hbehavior ⊢
  have hnoOvershoot :=
    nominalDramWriteOne_no_overshoot
      hinitial4 (by linarith) hbehavior
  intro time htime0 htimeH
  have hbounds := hnoOvershoot time htime0 htimeH
  exact ⟨hinitial0.trans hbounds.1, hbounds.2.trans (by norm_num)⟩

theorem dram_1t1c_write_one_assurance :
    AssuranceCase dram1T1C DramWriteBehavior Dram1T1CWriteOneAllowed
      dram1T1CWriteOneSourceBinding
      DramWriteOneNanosecondSpecification DramWriteRailDomain :=
  ⟨dram_1t1c_write_one_safe, dram_1t1c_write_one_realizable_all,
    dram_1t1c_write_one_domain⟩

theorem dram_1t1c_assurance :
    AssuranceCase dram1T1C Dram1T1CBehavior Dram1T1CExampleAllowed
      dram1T1CSourceBinding
      Dram1T1CValidityDomain Dram1T1CValidityDomain :=
  ⟨dram_1t1c_domain, dram_1t1c_realizable, dram_1t1c_domain⟩

#equation_guard Dram1T1CProgram forbids [Dram1T1CValidityDomain]
#equation_guard DramWriteProgram forbids
  [DramWriteOneNanosecondSpecification, DramWriteRailDomain]

end Examples.spice.dram_1t1c.proof
