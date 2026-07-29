import LeanModels.Python.Surface
import Examples.spice.dram_1t1c.proof

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
        storageCapacitance := 3 / 100000000000000 } := by proofs

theorem dram_1t1c_write_instance_from_source :
    Examples.spice.dram_1t1c.proof.dram1T1CWriteInstance =
      { threshold := 1
        beta := 1 / 10000
        storageCapacitance := 3 / 100000000000000 } := by proofs

theorem dram_1t1c_write_one_world_from_source
    (initialStorage horizon : ℝ) :
    Examples.spice.dram_1t1c.proof.dram1T1CWriteOneWorld
        initialStorage horizon =
      nominalDramWriteOneWorld initialStorage horizon := by proofs

theorem dram_1t1c_equation_manifest :
    EquationManifest Dram1T1CProgram [] := by proofs

theorem dram_1t1c_physics_only :
    Dram1T1CProgram.PhysicsOnly := by proofs

theorem dram_1t1c_realizable :
    RealizableUnder Dram1T1CBehavior
      Examples.spice.dram_1t1c.proof.Dram1T1CExampleAllowed := by proofs

theorem dram_1t1c_dae :
    SafeUnder Dram1T1CBehavior
      Examples.spice.dram_1t1c.proof.Dram1T1CExampleAllowed
      (fun world boundary _internal =>
        dram1T1CDAE.ACBehavesOn world world.environment.horizon
          boundary.storageVoltage) := by proofs

theorem dram_1t1c_domain :
    StaysWithinValidityDomain Dram1T1CBehavior
      Examples.spice.dram_1t1c.proof.Dram1T1CExampleAllowed
      Dram1T1CValidityDomain := by proofs

theorem dram_1t1c_hold_retention
    {world : Dram1T1CWorld} {boundary : Dram1T1CBoundary}
    (hallowed :
      Examples.spice.dram_1t1c.proof.Dram1T1CExampleAllowed world)
    (hmode : world.environment.mode = .hold)
    (hbehavior : Dram1T1CBehavior world boundary ()) :
    ∀ time ∈ Icc 0 world.environment.horizon,
      boundary.storageVoltage time =
        world.environment.initialVoltage := by proofs

theorem dram_1t1c_write_uses_mos1
    {world : Dram1T1CWorld}
    (hallowed :
      Examples.spice.dram_1t1c.proof.Dram1T1CExampleAllowed world)
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
        world.fabricated.storageCapacitance := by proofs

theorem dram_1t1c_hold_uses_mos1
    {world : Dram1T1CWorld}
    (hallowed :
      Examples.spice.dram_1t1c.proof.Dram1T1CExampleAllowed world)
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
        world.fabricated.storageCapacitance := by proofs

theorem dram_1t1c_write_zero_settles
    {world : Dram1T1CWorld} {boundary : Dram1T1CBoundary}
    (hallowed :
      Examples.spice.dram_1t1c.proof.Dram1T1CExampleAllowed world)
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
      world.environment.horizon := by proofs

theorem dram_1t1c_write_one_equation_manifest :
    EquationManifest DramWriteProgram [] := by proofs

theorem dram_1t1c_write_one_physics_only :
    DramWriteProgram.PhysicsOnly := by proofs

theorem dram_1t1c_write_one_settles
    {horizon : ℝ} {boundary : DramWriteBoundary}
    (hdeadline : (1 / 1000000000 : ℝ) ≤ horizon)
    (hbehavior :
      DramWriteBehavior
        (Examples.spice.dram_1t1c.proof.dram1T1CWriteOneWorld
          0 horizon) boundary ()) :
    DramWriteOneNanosecondSpecification
      (Examples.spice.dram_1t1c.proof.dram1T1CWriteOneWorld
        0 horizon) boundary () := by proofs

theorem dram_1t1c_write_one_realizable
    {horizon : ℝ} (hdeadline : (1 / 1000000000 : ℝ) ≤ horizon) :
    ∃ boundary,
      DramWriteBehavior
          (Examples.spice.dram_1t1c.proof.dram1T1CWriteOneWorld
            0 horizon) boundary () ∧
        DramWriteOneNanosecondSpecification
          (Examples.spice.dram_1t1c.proof.dram1T1CWriteOneWorld
            0 horizon) boundary () := by proofs

theorem dram_1t1c_write_one_safe :
    SafeUnder DramWriteBehavior
      Examples.spice.dram_1t1c.proof.Dram1T1CWriteOneAllowed
      DramWriteOneNanosecondSpecification := by proofs

theorem dram_1t1c_write_one_realizable_all :
    RealizableUnder DramWriteBehavior
      Examples.spice.dram_1t1c.proof.Dram1T1CWriteOneAllowed := by proofs

theorem dram_1t1c_write_one_domain :
    StaysWithinValidityDomain DramWriteBehavior
      Examples.spice.dram_1t1c.proof.Dram1T1CWriteOneAllowed
      DramWriteRailDomain := by proofs

theorem dram_1t1c_write_one_assurance :
    AssuranceCase dram1T1C DramWriteBehavior
      Examples.spice.dram_1t1c.proof.Dram1T1CWriteOneAllowed
      Examples.spice.dram_1t1c.proof.dram1T1CWriteOneSourceBinding
      DramWriteOneNanosecondSpecification DramWriteRailDomain := by proofs

theorem dram_1t1c_assurance :
    AssuranceCase dram1T1C Dram1T1CBehavior
      Examples.spice.dram_1t1c.proof.Dram1T1CExampleAllowed
      Examples.spice.dram_1t1c.proof.dram1T1CSourceBinding
      Dram1T1CValidityDomain Dram1T1CValidityDomain := by proofs

#assurance_report dram1T1C using dram_1t1c_assurance
  [dram_1t1c_equation_manifest, dram_1t1c_dae, dram_1t1c_hold_retention,
    dram_1t1c_hold_uses_mos1, dram_1t1c_write_uses_mos1,
    dram_1t1c_write_zero_settles]

#assurance_report dram1T1C using dram_1t1c_write_one_assurance
  [dram_1t1c_write_one_equation_manifest,
    dram_1t1c_write_one_safe, dram_1t1c_write_one_realizable_all,
    dram_1t1c_write_one_domain, dram_1t1c_write_one_settles]

#equation_report dram_1t1c_equation_manifest
#equation_report dram_1t1c_write_one_equation_manifest

#print axioms dram_1t1c_topology
#print axioms dram_1t1c_write_instance_from_source
#print axioms dram_1t1c_write_one_world_from_source
#print axioms dram_1t1c_equation_manifest
#print axioms dram_1t1c_physics_only
#print axioms dram_1t1c_realizable
#print axioms dram_1t1c_dae
#print axioms dram_1t1c_domain
#print axioms dram_1t1c_hold_retention
#print axioms dram_1t1c_write_uses_mos1
#print axioms dram_1t1c_hold_uses_mos1
#print axioms dram_1t1c_write_zero_settles
#print axioms dram_1t1c_write_one_equation_manifest
#print axioms dram_1t1c_write_one_physics_only
#print axioms dram_1t1c_write_one_settles
#print axioms dram_1t1c_write_one_realizable
#print axioms dram_1t1c_write_one_safe
#print axioms dram_1t1c_write_one_realizable_all
#print axioms dram_1t1c_write_one_domain
#print axioms dram_1t1c_write_one_assurance
#print axioms dram_1t1c_assurance
