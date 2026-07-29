import LeanModels.Spice.DramBank256x32
import LeanModels.Spice.DramBankCoreSpec
import LeanModels.Spice.DramBankSenseBridge
import LeanModels.Python.Surface

namespace Examples.spice.dram_bank_256x32.proof

open LeanModels.Circuit LeanModels.Spice

set_option maxRecDepth 100000

load_dram_bank dramBank256x32 from
  "Examples/spice/dram_bank_256x32/dram_bank_256x32.cir"
  rows 256 columns 32

noncomputable abbrev dramBank256x32Checked :
    CheckedDramBank dramBank256Rows dramBank256Columns :=
  dramBank256x32_checked

abbrev dramBank256x32Topology : DramBankTopologyWitness :=
  dramBank256x32_topology

noncomputable abbrev dramBank256x32Profile :
    DramBankCoreProfile dramBank256Rows dramBank256Columns :=
  dramBank256x32Checked.profile

theorem dram_bank_256x32_parameter_projection :
    dramBank256x32.toDramBankParameters
        dramBank256Rows dramBank256Columns =
      .ok dramBank256x32Checked.parameters := by
  exact dramBank256x32_parameter_projection

theorem dram_bank_256x32_topology_projection :
    DramBankTopologyValid dramBank256x32
      dramBank256Rows dramBank256Columns
      dramBank256x32Topology := by
  exact dramBank256x32_topology_projection

theorem dram_bank_256x32_differential_sense_connection_projection :
    DramBankDifferentialSenseConnectionValid dramBank256x32
      dramBank256Rows dramBank256Columns
      dramBank256x32Topology :=
  dram_bank_256x32_topology_projection.differentialSenseConnectionValid

theorem dram_bank_256x32_projection :
    dramBank256x32.toDramBank
        dramBank256Rows dramBank256Columns =
      .ok dramBank256x32Checked := by
  exact dramBank256x32_projection

theorem dram_bank_256x32_nominal_profile :
    DramBankCoreNominalProfile dramBank256x32Profile := by
  constructor
  · intro row column
    fin_cases column <;>
      norm_num [dramBank256x32Profile, dramBank256x32Checked,
        dramBank256x32_checked, CheckedDramBank.profile,
        DramBankSourceParameters.toCoreProfile,
        nominalDramCellInstance]
  · norm_num [dramBank256x32Profile, dramBank256x32Checked,
      dramBank256x32_checked, CheckedDramBank.profile,
      DramBankSourceParameters.toCoreProfile]

theorem dram_bank_256x32_sense_instance_projection :
    dramBank256x32Checked.parameters.toDifferentialSenseInstance =
      nominalDramDifferentialSenseInstance := by
  norm_num [dramBank256x32Checked, dramBank256x32_checked,
    DramBankSourceParameters.toDifferentialSenseInstance,
    nominalDramDifferentialSenseInstance]

theorem dram_bank_256x32_coupling_instance_projection
    (column : Fin dramBank256Columns) :
    dramBank256x32Checked.parameters.toSenseCouplingInstance column =
      nominalDramSenseCouplingInstance := by
  fin_cases column <;>
    norm_num [dramBank256x32Checked, dramBank256x32_checked,
      DramBankSourceParameters.toSenseCouplingInstance,
      nominalDramSenseCouplingInstance]

theorem dram_bank_256x32_coupling_equation_manifest :
    EquationManifest DramSenseCouplingProgram [] :=
  dramSenseCouplingEquationManifest

theorem dram_bank_256x32_coupling_initial_direction
    {bankWorld :
      DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    {couplingWorld : DramSenseCouplingWorld}
    {time : ℝ}
    {derivative : VectorState DramSenseCouplingIndex}
    (hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile
        bankWorld observation ())
    (hsupply : couplingWorld.environment.supply = 5)
    (column : Fin dramBank256Columns)
    (hinstance :
      couplingWorld.fabricated =
        dramBank256x32Checked.parameters.toSenseCouplingInstance column)
    (hresidual :
      dramSenseCouplingDAE.residual couplingWorld time
        (dramSenseCouplingInitialState
          (observation.activated.bitline column)
          (observation.prechargedBitline column))
        derivative) :
    if bankWorld.bits.bits bankWorld.row column then
      0 < derivative .trueLine - derivative .complementLine
    else
      derivative .trueLine - derivative .complementLine < 0 := by
  have hprecharge :=
    hbehavior.precharged_voltage_bounds
      dram_bank_256x32_nominal_profile column
  have hactivated :=
    hbehavior.activated_voltage
      dram_bank_256x32_nominal_profile column
  have hmargin :=
    hbehavior.activated_reference_margin
      dram_bank_256x32_nominal_profile column
  have hdirection :=
    dramSenseCoupling_nominal_initial_direction
      (hinstance.trans
        (dram_bank_256x32_coupling_instance_projection column))
      hsupply
      (bitline := observation.activated.bitline column)
      (reference := observation.prechargedBitline column)
      (by
        cases hbit : bankWorld.bits.bits bankWorld.row column
        · simp only [hbit, Bool.false_eq_true, if_false] at hactivated
          linarith [hactivated.1]
        · simp only [hbit, if_true] at hactivated
          linarith [hactivated.1])
      (by
        cases hbit : bankWorld.bits.bits bankWorld.row column
        · simp only [hbit, Bool.false_eq_true, if_false] at hactivated
          linarith [hactivated.2]
        · simp only [hbit, if_true] at hactivated
          linarith [hactivated.2])
      (by linarith [hprecharge.1])
      (by linarith [hprecharge.2])
      hresidual
  cases hbit : bankWorld.bits.bits bankWorld.row column
  · simp only [hbit, Bool.false_eq_true, if_false] at hmargin ⊢
    have hnegative :
        observation.activated.bitline column <
          observation.prechargedBitline column := by
      linarith
    have hnotPositive :
        ¬ observation.prechargedBitline column <
          observation.activated.bitline column := by
      linarith
    simpa [hnegative, hnotPositive] using hdirection
  · simp only [hbit, if_true] at hmargin ⊢
    have hpositive :
        observation.prechargedBitline column <
          observation.activated.bitline column := by
      linarith
    simpa [hpositive] using hdirection

theorem dram_bank_256x32_coupling_residual_realizable
    {couplingWorld : DramSenseCouplingWorld}
    {time : ℝ}
    {state : VectorState DramSenseCouplingIndex}
    (column : Fin dramBank256Columns)
    (hinstance :
      couplingWorld.fabricated =
        dramBank256x32Checked.parameters.toSenseCouplingInstance column)
    :
    ∃ derivative : VectorState DramSenseCouplingIndex,
      dramSenseCouplingDAE.residual couplingWorld time state derivative := by
  apply dramSenseCoupling_residual_realizable
  all_goals
    rw [hinstance,
      dram_bank_256x32_coupling_instance_projection column]
    norm_num [nominalDramSenseCouplingInstance]

theorem dram_bank_256x32_coupling_conserves_voltage_sums
    {couplingWorld : DramSenseCouplingWorld}
    {boundary : DramSenseCouplingBoundary}
    (column : Fin dramBank256Columns)
    (hinstance :
      couplingWorld.fabricated =
        dramBank256x32Checked.parameters.toSenseCouplingInstance column)
    (hbehavior :
      DramSenseCouplingBehavior couplingWorld boundary ()) :
    ∀ time ∈ Set.Icc 0 couplingWorld.environment.horizon,
      boundary.voltage time .bitline +
            boundary.voltage time .trueLine =
          boundary.voltage 0 .bitline +
            boundary.voltage 0 .trueLine ∧
        boundary.voltage time .reference +
            boundary.voltage time .complementLine =
          boundary.voltage 0 .reference +
            boundary.voltage 0 .complementLine := by
  intro time htime
  have hcharge :=
    dramSenseCoupling_behavior_conserves_pair_charge
      hbehavior time htime
  rw [hinstance,
    dram_bank_256x32_coupling_instance_projection column] at hcharge
  norm_num [dramSenseCouplingBitPairCharge,
    dramSenseCouplingReferencePairCharge,
    nominalDramSenseCouplingInstance] at hcharge ⊢
  constructor
  · linarith [hcharge.1]
  · linarith [hcharge.2]

noncomputable def dramBank256x32CouplingWorld
    (observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns)
    (column : Fin dramBank256Columns)
    (horizon : ℝ) : DramSenseCouplingWorld :=
  deterministicWorld
    (dramBank256x32Checked.parameters.toSenseCouplingInstance column)
    { supply := 5
      initialBitline := observation.activated.bitline column
      initialReference := observation.prechargedBitline column
      initialTrue := 5 / 2
      initialComplement := 5 / 2
      horizon }

theorem dram_bank_256x32_coupling_allowed
    {bankWorld :
      DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    (hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile
        bankWorld observation ())
    (column : Fin dramBank256Columns)
    {horizon : ℝ}
    (hhorizon : 0 ≤ horizon) :
    DramSenseCouplingNominalAllowed
      (dramBank256x32CouplingWorld observation column horizon) := by
  have hprecharge :=
    hbehavior.precharged_voltage_bounds
      dram_bank_256x32_nominal_profile column
  have hactivated :=
    hbehavior.activated_voltage
      dram_bank_256x32_nominal_profile column
  unfold DramSenseCouplingNominalAllowed
    dramBank256x32CouplingWorld
  dsimp only [deterministicWorld]
  refine
    ⟨dram_bank_256x32_coupling_instance_projection column,
      rfl, ?_, ?_, ?_, ?_, rfl, rfl, hhorizon⟩
  · cases hbit : bankWorld.bits.bits bankWorld.row column
    · simp only [hbit, Bool.false_eq_true, if_false] at hactivated
      linarith [hactivated.1]
    · simp only [hbit, if_true] at hactivated
      linarith [hactivated.1]
  · cases hbit : bankWorld.bits.bits bankWorld.row column
    · simp only [hbit, Bool.false_eq_true, if_false] at hactivated
      linarith [hactivated.2]
    · simp only [hbit, if_true] at hactivated
      linarith [hactivated.2]
  · linarith [hprecharge.1]
  · linarith [hprecharge.2]

theorem dram_bank_256x32_coupling_transient_realizable
    {bankWorld :
      DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    (hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile
        bankWorld observation ())
    (column : Fin dramBank256Columns)
    {horizon : ℝ}
    (hhorizon : 0 ≤ horizon) :
    ∃ boundary,
      DramSenseCouplingBehavior
        (dramBank256x32CouplingWorld observation column horizon)
        boundary () := by
  obtain ⟨boundary, internal, hcoupling⟩ :=
    dramSenseCoupling_nominal_realizable
      (dramBank256x32CouplingWorld observation column horizon)
      (dram_bank_256x32_coupling_allowed
        hbehavior column hhorizon)
  cases internal
  exact ⟨boundary, hcoupling⟩

theorem dram_bank_256x32_coupling_transient_stays_in_domain
    {bankWorld :
      DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    (hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile
        bankWorld observation ())
    (column : Fin dramBank256Columns)
    {horizon : ℝ}
    (hhorizon : 0 ≤ horizon) :
    ∀ time ∈ Set.Icc 0 horizon,
      ∀ index,
        2 ≤
            (nominalDramSenseCouplingBoundary
              (observation.activated.bitline column)
              (observation.prechargedBitline column)).voltage time index ∧
          (nominalDramSenseCouplingBoundary
              (observation.activated.bitline column)
              (observation.prechargedBitline column)).voltage time index ≤ 3 := by
  exact nominalDramSenseCoupling_behavior_stays_in_domain
    (dram_bank_256x32_coupling_allowed
      hbehavior column hhorizon)

theorem dram_bank_256x32_coupling_establishes_ready
    {bankWorld :
      DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    {senseWorld : DramDifferentialSenseWorld}
    (hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile
        bankWorld observation ())
    (hsupply : senseWorld.environment.supply = 5)
    (column : Fin dramBank256Columns)
    {time : ℝ}
    (htime : 0 < time) :
    DramDifferentialSenseCouplingReady senseWorld
      (bankWorld.bits.bits bankWorld.row column)
      (dramSenseCouplingLatchState
        (observation.activated.bitline column)
        (observation.prechargedBitline column)
        time) := by
  have hprecharge :=
    hbehavior.precharged_voltage_bounds
      dram_bank_256x32_nominal_profile column
  have hactivated :=
    hbehavior.activated_voltage
      dram_bank_256x32_nominal_profile column
  have hmargin :=
    hbehavior.activated_reference_margin
      dram_bank_256x32_nominal_profile column
  apply dramSenseCoupling_nominal_establishes_ready hsupply
  · cases hbit : bankWorld.bits.bits bankWorld.row column
    · simp only [hbit, Bool.false_eq_true, if_false] at hactivated
      linarith [hactivated.1]
    · simp only [hbit, if_true] at hactivated
      linarith [hactivated.1]
  · cases hbit : bankWorld.bits.bits bankWorld.row column
    · simp only [hbit, Bool.false_eq_true, if_false] at hactivated
      linarith [hactivated.2]
    · simp only [hbit, if_true] at hactivated
      linarith [hactivated.2]
  · linarith [hprecharge.1]
  · linarith [hprecharge.2]
  · exact htime
  · cases hbit : bankWorld.bits.bits bankWorld.row column
    · simp only [hbit, Bool.false_eq_true, if_false] at hmargin ⊢
      constructor
      · linarith
      · linarith [hprecharge.2]
    · simp only [hbit, if_true] at hactivated hmargin ⊢
      constructor
      · linarith [hactivated.1]
      · linarith [hprecharge.2]

theorem dram_bank_256x32_sense_coupling_ready_regeneration
    {bankWorld :
      DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {senseWorld : DramDifferentialSenseWorld}
    {time : ℝ}
    {state derivative : VectorState DramDifferentialSenseIndex}
    (hsupply : senseWorld.environment.supply = 5)
    (hinstance :
      senseWorld.fabricated =
        dramBank256x32Checked.parameters.toDifferentialSenseInstance)
    (column : Fin dramBank256Columns)
    (hready :
      DramDifferentialSenseCouplingReady senseWorld
        (bankWorld.bits.bits bankWorld.row column) state)
    (hresidual :
      dramDifferentialSenseDAE.residual senseWorld time state derivative) :
    if bankWorld.bits.bits bankWorld.row column then
      0 < derivative .trueLine - derivative .complementLine
    else
      derivative .trueLine - derivative .complementLine < 0 :=
  dramDifferentialSense_nominal_coupling_ready_regeneration
    hsupply
    (hinstance.trans dram_bank_256x32_sense_instance_projection)
    hready hresidual

theorem dram_bank_256x32_coupled_regeneration_after_positive_time
    {bankWorld :
      DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    {senseWorld : DramDifferentialSenseWorld}
    {couplingTime latchTime : ℝ}
    {derivative : VectorState DramDifferentialSenseIndex}
    (hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile
        bankWorld observation ())
    (hsupply : senseWorld.environment.supply = 5)
    (hinstance :
      senseWorld.fabricated =
        dramBank256x32Checked.parameters.toDifferentialSenseInstance)
    (column : Fin dramBank256Columns)
    (hcouplingTime : 0 < couplingTime)
    (hresidual :
      dramDifferentialSenseDAE.residual senseWorld latchTime
        (dramSenseCouplingLatchState
          (observation.activated.bitline column)
          (observation.prechargedBitline column)
          couplingTime)
        derivative) :
    if bankWorld.bits.bits bankWorld.row column then
      0 < derivative .trueLine - derivative .complementLine
    else
      derivative .trueLine - derivative .complementLine < 0 := by
  apply dram_bank_256x32_sense_coupling_ready_regeneration
    hsupply hinstance column
  · exact dram_bank_256x32_coupling_establishes_ready
      hbehavior hsupply column hcouplingTime
  · exact hresidual

/-- The source-derived coupling endpoint initializes an inhabited,
finite-horizon behavior of the projected four-MOS/two-capacitor latch. -/
theorem dram_bank_256x32_coupled_latch_realizable
    {bankWorld :
      DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    {senseWorld : DramDifferentialSenseWorld}
    {couplingTime : ℝ}
    (hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile
        bankWorld observation ())
    (hsupply : senseWorld.environment.supply = 5)
    (hinstance :
      senseWorld.fabricated =
        dramBank256x32Checked.parameters.toDifferentialSenseInstance)
    (hhorizon : 0 ≤ senseWorld.environment.horizon)
    (column : Fin dramBank256Columns)
    (hcouplingTime : 0 < couplingTime)
    (hinitialTrue :
      senseWorld.environment.initialTrue =
        dramSenseCouplingLatchState
          (observation.activated.bitline column)
          (observation.prechargedBitline column)
          couplingTime .trueLine)
    (hinitialComplement :
      senseWorld.environment.initialComplement =
        dramSenseCouplingLatchState
          (observation.activated.bitline column)
          (observation.prechargedBitline column)
          couplingTime .complementLine) :
    ∃ boundary : DramDifferentialSenseBoundary,
      DramDifferentialSenseBehavior senseWorld boundary () ∧
      ∀ time ∈ Set.Icc (0 : ℝ) senseWorld.environment.horizon,
        boundary.voltage time .trueLine ∈ Set.Icc (0 : ℝ) 5 ∧
          boundary.voltage time .complementLine ∈
            Set.Icc (0 : ℝ) 5 := by
  apply
    dramDifferentialSense_nominal_coupling_ready_realizable
      hsupply
      (hinstance.trans dram_bank_256x32_sense_instance_projection)
      hhorizon
  · exact dram_bank_256x32_coupling_establishes_ready
      hbehavior hsupply column hcouplingTime
  · exact hinitialTrue
  · exact hinitialComplement

/-- After the physical coupling phase, the bank has an inhabited nominal
latch trajectory whose correctly signed differential never decreases. The
same trajectory satisfies the source-projected primitive latch DAE and stays
inside the supply rails for the whole requested horizon. -/
theorem dram_bank_256x32_coupled_latch_margin_realizable
    {bankWorld :
      DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    {senseWorld : DramDifferentialSenseWorld}
    {couplingTime : ℝ}
    (hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile
        bankWorld observation ())
    (hsupply : senseWorld.environment.supply = 5)
    (hinstance :
      senseWorld.fabricated =
        dramBank256x32Checked.parameters.toDifferentialSenseInstance)
    (hhorizon : 0 ≤ senseWorld.environment.horizon)
    (column : Fin dramBank256Columns)
    (hcouplingTime : 0 < couplingTime) :
    ∃ trajectory : ℝ → DramDifferentialSensePair,
      trajectory 0 =
          dramDifferentialSenseStatePair
            (dramSenseCouplingLatchState
              (observation.activated.bitline column)
              (observation.prechargedBitline column)
              couplingTime) ∧
      (∀ time ∈ Set.Icc (0 : ℝ) senseWorld.environment.horizon,
        HasDerivWithinAt trajectory
          (dramDifferentialSenseNominalClampedPairRate
            (trajectory time))
          (Set.Icc (0 : ℝ) senseWorld.environment.horizon) time) ∧
      (∀ time ∈ Set.Icc (0 : ℝ) senseWorld.environment.horizon,
        (trajectory time).1 ∈ Set.Icc (0 : ℝ) 5 ∧
          (trajectory time).2 ∈ Set.Icc (0 : ℝ) 5) ∧
      MonotoneOn
        (fun time =>
          dramDifferentialSenseSignedPairMargin
            (bankWorld.bits.bits bankWorld.row column)
            (trajectory time))
        (Set.Icc (0 : ℝ) senseWorld.environment.horizon) ∧
      ∀ time ∈ Set.Icc (0 : ℝ) senseWorld.environment.horizon,
        dramDifferentialSenseDAE.residual senseWorld time
          (dramDifferentialSensePairState (trajectory time))
          (dramDifferentialSensePairState
            (dramDifferentialSenseNominalClampedPairRate
              (trajectory time))) := by
  apply
    dramDifferentialSense_nominal_coupling_ready_margin_realizable
      hsupply
      (hinstance.trans dram_bank_256x32_sense_instance_projection)
      hhorizon
  exact dram_bank_256x32_coupling_establishes_ready
    hbehavior hsupply column hcouplingTime

/-- Every selected bank column has a source-derived finite-resolution
certificate after physical coupling. The target may be any signed margin
between the delivered margin and full 5 V rail separation. -/
theorem dram_bank_256x32_coupled_latch_resolves
    {bankWorld :
      DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    {senseWorld : DramDifferentialSenseWorld}
    {couplingTime required : ℝ}
    (hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile
        bankWorld observation ())
    (hsupply : senseWorld.environment.supply = 5)
    (hinstance :
      senseWorld.fabricated =
        dramBank256x32Checked.parameters.toDifferentialSenseInstance)
    (hhorizon : 0 ≤ senseWorld.environment.horizon)
    (column : Fin dramBank256Columns)
    (hcouplingTime : 0 < couplingTime)
    (hrequiredLower :
      dramDifferentialSenseSignedPairMargin
          (bankWorld.bits.bits bankWorld.row column)
          (dramDifferentialSenseStatePair
            (dramSenseCouplingLatchState
              (observation.activated.bitline column)
              (observation.prechargedBitline column)
              couplingTime)) ≤ required)
    (hrequiredUpper : required < 5) :
    Nonempty
      (DramDifferentialSenseResolutionWitness senseWorld
        (bankWorld.bits.bits bankWorld.row column)
        (dramDifferentialSenseStatePair
          (dramSenseCouplingLatchState
            (observation.activated.bitline column)
            (observation.prechargedBitline column)
            couplingTime))
        required) := by
  apply
    dramDifferentialSense_nominal_coupling_ready_resolution_realizable
      required hsupply
      (hinstance.trans dram_bank_256x32_sense_instance_projection)
      hhorizon
  · exact
      dram_bank_256x32_coupling_establishes_ready
        hbehavior hsupply column hcouplingTime
  · exact hrequiredLower
  · exact hrequiredUpper

theorem dram_bank_256x32_sense_coupled_residual_realizable
    {senseWorld : DramDifferentialSenseWorld}
    {time : ℝ}
    {state : VectorState DramDifferentialSenseIndex}
    (hinstance :
      senseWorld.fabricated =
        dramBank256x32Checked.parameters.toDifferentialSenseInstance) :
    ∃ derivative : VectorState DramDifferentialSenseIndex,
      dramDifferentialSenseDAE.residual senseWorld time state derivative := by
  apply dramDifferentialSense_residual_realizable
  · rw [hinstance, dram_bank_256x32_sense_instance_projection]
    norm_num [nominalDramDifferentialSenseInstance]
  · rw [hinstance, dram_bank_256x32_sense_instance_projection]
    norm_num [nominalDramDifferentialSenseInstance]

theorem dram_bank_256x32_read_equation_manifest :
    EquationManifest
      (DramBankCoreReadProgram dramBank256x32Profile)
      ["legacy two-inverter sense endpoint contract"] :=
  dramBankCoreReadEquationManifest

theorem dram_bank_256x32_write_equation_manifest :
    EquationManifest
      (DramBankCoreWriteProgram dramBank256x32Profile)
      ["read endpoint phase"] :=
  dramBankCoreWriteEquationManifest

noncomputable def dramBank256x32ReadSourceBinding :
    SourceBinding dramBank256x32
      (DramBankCoreReadBehavior dramBank256x32Profile)
      (DramBankCoreReadAllowed dramBank256x32Profile) :=
  SourceBinding.checked
    (fun source =>
      source.toDramBank dramBank256Rows dramBank256Columns)
    dramBank256x32 dramBank256x32Checked
    dram_bank_256x32_projection
    (fun artifact => DramBankCoreReadBehavior artifact.profile)
    (fun artifact => DramBankCoreReadAllowed artifact.profile)

theorem dram_bank_256x32_read_safe :
    SafeUnder (DramBankCoreReadBehavior dramBank256x32Profile)
      (DramBankCoreReadAllowed dramBank256x32Profile)
      DramBankCoreReadSpecification :=
  dramBankCore_read_safe dramBank256x32Profile

theorem dram_bank_256x32_read_realizable :
    RealizableUnder (DramBankCoreReadBehavior dramBank256x32Profile)
      (DramBankCoreReadAllowed dramBank256x32Profile) :=
  dramBankCore_read_realizable dramBank256x32Profile

theorem dram_bank_256x32_read_domain :
    StaysWithinValidityDomain
      (DramBankCoreReadBehavior dramBank256x32Profile)
      (DramBankCoreReadAllowed dramBank256x32Profile)
      DramBankCoreReadDomain :=
  dramBankCore_read_domain dramBank256x32Profile

/-- The finite-time bitline precharge band is derived from the enabled MOS1,
the 300 fF bitline capacitor, and their continuous DAE. -/
theorem dram_bank_256x32_precharge_derived
    {world : DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    (hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile world observation ()) :
    ∀ column,
      247 / 100 ≤ observation.prechargedBitline column ∧
        observation.prechargedBitline column ≤ 5 / 2 :=
  hbehavior.precharged_voltage_bounds
    dram_bank_256x32_nominal_profile

/-- Every selected address delivers at least `3/22 V` against an otherwise
precharged reference bitline, without any per-cell proof enumeration. -/
theorem dram_bank_256x32_reference_margin
    {world : DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    (hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile world observation ()) :
    ∀ column,
      if world.bits.bits world.row column then
        observation.prechargedBitline column + 3 / 22 ≤
          observation.activated.bitline column
      else
        observation.activated.bitline column + 3 / 22 ≤
          observation.prechargedBitline column :=
  hbehavior.activated_reference_margin
    dram_bank_256x32_nominal_profile

/-- The source-projected latch locally amplifies the bank's derived
bitline/reference ordering. The literal deck now contains the latch and both
coupling gates; deriving the latch-node state reached by the finite coupling
phase remains a separate transient-refinement obligation. -/
theorem dram_bank_256x32_sense_local_regeneration
    {bankWorld :
      DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    {senseWorld : DramDifferentialSenseWorld}
    {time : ℝ}
    {derivative : VectorState DramDifferentialSenseIndex}
    (hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile
        bankWorld observation ())
    (hsupply : senseWorld.environment.supply = 5)
    (hinstance :
      senseWorld.fabricated =
        dramBank256x32Checked.parameters.toDifferentialSenseInstance)
    (column : Fin dramBank256Columns)
    (hresidual :
      dramDifferentialSenseDAE.residual senseWorld time
        (dramBankDifferentialSenseInitialState
          (observation.activated.bitline column)
          (observation.prechargedBitline column))
        derivative) :
    if bankWorld.bits.bits bankWorld.row column then
      0 < derivative .trueLine - derivative .complementLine
    else
      derivative .trueLine - derivative .complementLine < 0 :=
  hbehavior.differential_sense_local_regeneration
    dram_bank_256x32_nominal_profile hsupply
      (hinstance.trans dram_bank_256x32_sense_instance_projection)
      column hresidual

theorem dram_bank_256x32_sense_residual_realizable
    {bankWorld :
      DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    {senseWorld : DramDifferentialSenseWorld}
    {time : ℝ}
    (_hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile
        bankWorld observation ())
    (hinstance :
      senseWorld.fabricated =
        dramBank256x32Checked.parameters.toDifferentialSenseInstance)
    (column : Fin dramBank256Columns) :
    ∃ derivative : VectorState DramDifferentialSenseIndex,
      dramDifferentialSenseDAE.residual senseWorld time
        (dramBankDifferentialSenseInitialState
          (observation.activated.bitline column)
          (observation.prechargedBitline column))
        derivative := by
  apply dramBankDifferentialSense_initial_residual_realizable
  · rw [hinstance, dram_bank_256x32_sense_instance_projection]
    norm_num [nominalDramDifferentialSenseInstance]
  · rw [hinstance, dram_bank_256x32_sense_instance_projection]
    norm_num [nominalDramDifferentialSenseInstance]

/-- Every unselected cell follows its source-parameterized 1T1C hold DAE.
Preservation is derived from that trajectory and endpoint wiring, not imported
as a bank contract. -/
theorem dram_bank_256x32_unselected_derived
    {world : DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    (hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile world observation ()) :
    ∀ otherRow, otherRow ≠ world.row →
      ∀ column,
        observation.restored.storage otherRow column =
          dramBankCoreStoredVoltage
            (world.bits.bits otherRow column) := by
  intro otherRow hother column
  simpa [dramBankCoreInitialEndpoint] using
    hbehavior.unselected_preserved otherRow hother column

/-- Every selected address returns the expected bit, and every restored cell
remains in the voltage band representing its stored bit. Both selected-row
bands come from the finite-horizon restore DAE. -/
theorem dram_bank_256x32_read_correct
    {world : DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    (hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile world observation ()) :
    observation.dataOut =
        logicVoltage (world.bits.bits world.row world.column) ∧
      ∀ row column,
        DramBankCoreStorageRepresents
          (observation.restored.storage row column)
          (world.bits.bits row column) := by
  exact dram_bank_256x32_read_safe world observation ()
    dram_bank_256x32_nominal_profile hbehavior

theorem dram_bank_256x32_read_assurance :
    AssuranceCase dramBank256x32
      (DramBankCoreReadBehavior dramBank256x32Profile)
      (DramBankCoreReadAllowed dramBank256x32Profile)
      dramBank256x32ReadSourceBinding
      DramBankCoreReadSpecification DramBankCoreReadDomain :=
  ⟨dram_bank_256x32_read_safe, dram_bank_256x32_read_realizable,
    dram_bank_256x32_read_domain⟩

noncomputable def dramBank256x32WriteSourceBinding :
    SourceBinding dramBank256x32
      (DramBankCoreWriteBehavior dramBank256x32Profile)
      (DramBankCoreWriteAllowed dramBank256x32Profile) :=
  SourceBinding.checked
    (fun source =>
      source.toDramBank dramBank256Rows dramBank256Columns)
    dramBank256x32 dramBank256x32Checked
    dram_bank_256x32_projection
    (fun artifact => DramBankCoreWriteBehavior artifact.profile)
    (fun artifact => DramBankCoreWriteAllowed artifact.profile)

theorem dram_bank_256x32_write_safe :
    SafeUnder (DramBankCoreWriteBehavior dramBank256x32Profile)
      (DramBankCoreWriteAllowed dramBank256x32Profile)
      DramBankCoreWriteSpecification :=
  dramBankCore_write_safe dramBank256x32Profile

theorem dram_bank_256x32_write_realizable :
    RealizableUnder (DramBankCoreWriteBehavior dramBank256x32Profile)
      (DramBankCoreWriteAllowed dramBank256x32Profile) :=
  dramBankCore_write_realizable dramBank256x32Profile

theorem dram_bank_256x32_write_domain :
    StaysWithinValidityDomain
      (DramBankCoreWriteBehavior dramBank256x32Profile)
      (DramBankCoreWriteAllowed dramBank256x32Profile)
      DramBankCoreWriteDomain :=
  dramBankCore_write_domain dramBank256x32Profile

/-- Every cell outside the selected address continues to represent its prior
bit. Unselected rows are exactly preserved by cutoff hold; selected-row cells
on other columns continue their sense-clamped restore trajectories. -/
theorem dram_bank_256x32_write_unselected_derived
    {world : DramBankCoreWriteWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreWriteObservation dramBank256Rows dramBank256Columns}
    (hbehavior :
      DramBankCoreWriteBehavior dramBank256x32Profile world observation ()) :
    ∀ row column,
      row ≠ world.row ∨ column ≠ world.column →
      DramBankCoreStorageRepresents
        (observation.after.storage row column)
        (world.bits.bits row column) := by
  intro row column hother
  have hsafe := dram_bank_256x32_write_safe world observation ()
    dram_bank_256x32_nominal_profile hbehavior row column
  rw [DramMatrixState.write_other _ _ _ _ _ _ hother] at hsafe
  exact hsafe

/-- Every selected write is derived from the projected 1T1C transient: low
writes enter `[0 V, 1 V]`, high writes enter `[3 V, 4 V]`, and every other
cell continues to represent its prior bit. -/
theorem dram_bank_256x32_write_correct
    {world : DramBankCoreWriteWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreWriteObservation dramBank256Rows dramBank256Columns}
    (hbehavior :
      DramBankCoreWriteBehavior dramBank256x32Profile world observation ()) :
    ∀ row column,
      DramBankCoreStorageRepresents
        (observation.after.storage row column)
          ((world.bits.write world.row world.column world.value).bits
            row column) := by
  exact dram_bank_256x32_write_safe world observation ()
    dram_bank_256x32_nominal_profile hbehavior

theorem dram_bank_256x32_write_assurance :
    AssuranceCase dramBank256x32
      (DramBankCoreWriteBehavior dramBank256x32Profile)
      (DramBankCoreWriteAllowed dramBank256x32Profile)
      dramBank256x32WriteSourceBinding
      DramBankCoreWriteSpecification DramBankCoreWriteDomain :=
  ⟨dram_bank_256x32_write_safe, dram_bank_256x32_write_realizable,
    dram_bank_256x32_write_domain⟩

theorem dram_bank_256x32_read_refines_step
    {world : DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    (hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile world observation ()) :
    ∃ response after,
      DramBankStep world.bits
          (.read world.row world.column) response after ∧
        DramBankCoreReadResponseObserved observation response ∧
        DramBankCoreEndpointRepresents observation.restored after :=
  dramBankCore_read_refines_step
    dram_bank_256x32_nominal_profile hbehavior

theorem dram_bank_256x32_write_refines_step
    {world : DramBankCoreWriteWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreWriteObservation dramBank256Rows dramBank256Columns}
    (hbehavior :
      DramBankCoreWriteBehavior dramBank256x32Profile world observation ()) :
    ∃ after,
      DramBankStep world.bits
          (.write world.row world.column world.value)
          .acknowledged after ∧
        DramBankCoreEndpointRepresents observation.after after :=
  dramBankCore_write_refines_step
    dram_bank_256x32_nominal_profile hbehavior

#equation_guard DramBankCoreReadProgram forbids
  [DramBankCoreReadSpecification, DramBankCoreWriteSpecification]

#equation_guard DramSenseCouplingProgram forbids
  [DramBankCoreReadSpecification, DramBankCoreWriteSpecification]

#equation_guard DramPrechargeProgram forbids
  [DramBankCoreReadSpecification, DramBankCoreWriteSpecification]

#equation_guard DramBankCoreWriteProgram forbids
  [DramBankCoreReadSpecification, DramBankCoreWriteSpecification]

#assurance_report dramBank256x32 using dram_bank_256x32_read_assurance
  [dram_bank_256x32_read_equation_manifest,
    dram_bank_256x32_coupling_equation_manifest,
    dram_bank_256x32_coupling_instance_projection,
    dram_bank_256x32_coupling_initial_direction,
    dram_bank_256x32_coupling_residual_realizable,
    dram_bank_256x32_coupling_conserves_voltage_sums,
    dram_bank_256x32_coupling_allowed,
    dram_bank_256x32_coupling_transient_realizable,
    dram_bank_256x32_coupling_transient_stays_in_domain,
    dram_bank_256x32_coupling_establishes_ready,
    dram_bank_256x32_differential_sense_connection_projection,
    dram_bank_256x32_sense_instance_projection,
    dram_bank_256x32_sense_coupling_ready_regeneration,
    dram_bank_256x32_coupled_regeneration_after_positive_time,
    dram_bank_256x32_coupled_latch_realizable,
    dram_bank_256x32_coupled_latch_margin_realizable,
    dram_bank_256x32_coupled_latch_resolves,
    dram_bank_256x32_sense_coupled_residual_realizable,
    dram_bank_256x32_precharge_derived,
    dram_bank_256x32_reference_margin,
    dram_bank_256x32_sense_local_regeneration,
    dram_bank_256x32_sense_residual_realizable,
    dram_bank_256x32_unselected_derived,
    dram_bank_256x32_read_correct, dram_bank_256x32_read_refines_step]

#assurance_report dramBank256x32 using dram_bank_256x32_write_assurance
  [dram_bank_256x32_write_equation_manifest,
    dram_bank_256x32_write_unselected_derived,
    dram_bank_256x32_write_correct, dram_bank_256x32_write_refines_step]

#equation_report dram_bank_256x32_read_equation_manifest
#equation_report dram_bank_256x32_coupling_equation_manifest
#equation_report dramPrechargeEquationManifest
#equation_report dram_bank_256x32_write_equation_manifest

#print axioms dram_bank_256x32_coupling_instance_projection
#print axioms dram_bank_256x32_coupling_equation_manifest
#print axioms dram_bank_256x32_coupling_initial_direction
#print axioms dram_bank_256x32_coupling_residual_realizable
#print axioms dram_bank_256x32_coupling_conserves_voltage_sums
#print axioms dram_bank_256x32_coupling_allowed
#print axioms dram_bank_256x32_coupling_transient_realizable
#print axioms dram_bank_256x32_coupling_transient_stays_in_domain
#print axioms dram_bank_256x32_coupling_establishes_ready
#print axioms dram_bank_256x32_reference_margin
#print axioms dram_bank_256x32_differential_sense_connection_projection
#print axioms dram_bank_256x32_sense_instance_projection
#print axioms dram_bank_256x32_sense_coupling_ready_regeneration
#print axioms dram_bank_256x32_coupled_regeneration_after_positive_time
#print axioms dram_bank_256x32_coupled_latch_realizable
#print axioms dram_bank_256x32_coupled_latch_margin_realizable
#print axioms dram_bank_256x32_coupled_latch_resolves
#print axioms dram_bank_256x32_sense_coupled_residual_realizable
#print axioms dram_bank_256x32_sense_local_regeneration
#print axioms dram_bank_256x32_sense_residual_realizable

end Examples.spice.dram_bank_256x32.proof
