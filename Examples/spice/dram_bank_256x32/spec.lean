import Examples.spice.dram_bank_256x32.proof

open LeanModels.Circuit LeanModels.Spice
open Examples.spice.dram_bank_256x32.proof

theorem dram_bank_256x32_parameter_projection :
    dramBank256x32.toDramBankParameters
        dramBank256Rows dramBank256Columns =
      .ok dramBank256x32Checked.parameters := by proofs

theorem dram_bank_256x32_topology_projection :
    DramBankTopologyValid dramBank256x32
      dramBank256Rows dramBank256Columns
      dramBank256x32Topology := by proofs

theorem dram_bank_256x32_differential_sense_connection_projection :
    DramBankDifferentialSenseConnectionValid dramBank256x32
      dramBank256Rows dramBank256Columns
      dramBank256x32Topology := by proofs

theorem dram_bank_256x32_projection :
    dramBank256x32.toDramBank
        dramBank256Rows dramBank256Columns =
      .ok dramBank256x32Checked := by proofs

theorem dram_bank_256x32_nominal_profile :
    DramBankCoreNominalProfile dramBank256x32Profile := by proofs

theorem dram_bank_256x32_sense_instance_projection :
    dramBank256x32Checked.parameters.toDifferentialSenseInstance =
      nominalDramDifferentialSenseInstance := by proofs

theorem dram_bank_256x32_coupling_instance_projection
    (column : Fin dramBank256Columns) :
    dramBank256x32Checked.parameters.toSenseCouplingInstance column =
      nominalDramSenseCouplingInstance := by proofs

theorem dram_bank_256x32_coupling_equation_manifest :
    EquationManifest DramSenseCouplingProgram [] := by proofs

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
      derivative .trueLine - derivative .complementLine < 0 := by proofs

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
  proofs

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
            boundary.voltage 0 .complementLine := by proofs

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
      (dramBank256x32CouplingWorld observation column horizon) := by proofs

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
        boundary () := by proofs

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
  proofs

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
        time) := by proofs

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
      derivative .trueLine - derivative .complementLine < 0 := by proofs

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
      derivative .trueLine - derivative .complementLine < 0 := by proofs

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
            Set.Icc (0 : ℝ) 5 := by proofs

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
              (trajectory time))) := by proofs

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
        required) := by proofs

theorem dram_bank_256x32_sense_coupled_residual_realizable
    {senseWorld : DramDifferentialSenseWorld}
    {time : ℝ}
    {state : VectorState DramDifferentialSenseIndex}
    (hinstance :
      senseWorld.fabricated =
        dramBank256x32Checked.parameters.toDifferentialSenseInstance) :
    ∃ derivative : VectorState DramDifferentialSenseIndex,
      dramDifferentialSenseDAE.residual senseWorld time state derivative :=
  by proofs

theorem dram_bank_256x32_read_equation_manifest :
    EquationManifest
      (DramBankCoreReadProgram dramBank256x32Profile)
      ["legacy two-inverter sense endpoint contract"] := by proofs

theorem dram_bank_256x32_write_equation_manifest :
    EquationManifest
      (DramBankCoreWriteProgram dramBank256x32Profile)
      ["read endpoint phase"] := by proofs

theorem dram_bank_256x32_read_safe :
    SafeUnder (DramBankCoreReadBehavior dramBank256x32Profile)
      (DramBankCoreReadAllowed dramBank256x32Profile)
      DramBankCoreReadSpecification := by proofs

theorem dram_bank_256x32_read_realizable :
    RealizableUnder (DramBankCoreReadBehavior dramBank256x32Profile)
      (DramBankCoreReadAllowed dramBank256x32Profile) := by proofs

theorem dram_bank_256x32_read_domain :
    StaysWithinValidityDomain
      (DramBankCoreReadBehavior dramBank256x32Profile)
      (DramBankCoreReadAllowed dramBank256x32Profile)
      DramBankCoreReadDomain := by proofs

theorem dram_bank_256x32_precharge_derived
    {world : DramBankCoreReadWorld dramBank256Rows dramBank256Columns}
    {observation :
      DramBankCoreReadObservation dramBank256Rows dramBank256Columns}
    (hbehavior :
      DramBankCoreReadBehavior dramBank256x32Profile world observation ()) :
    ∀ column,
      247 / 100 ≤ observation.prechargedBitline column ∧
        observation.prechargedBitline column ≤ 5 / 2 := by proofs

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
          observation.prechargedBitline column := by proofs

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
      derivative .trueLine - derivative .complementLine < 0 := by proofs

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
        derivative := by proofs

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
            (world.bits.bits otherRow column) := by proofs

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
          (world.bits.bits row column) := by proofs

theorem dram_bank_256x32_read_assurance :
    AssuranceCase dramBank256x32
      (DramBankCoreReadBehavior dramBank256x32Profile)
      (DramBankCoreReadAllowed dramBank256x32Profile)
      dramBank256x32ReadSourceBinding
      DramBankCoreReadSpecification DramBankCoreReadDomain := by proofs

theorem dram_bank_256x32_write_safe :
    SafeUnder (DramBankCoreWriteBehavior dramBank256x32Profile)
      (DramBankCoreWriteAllowed dramBank256x32Profile)
      DramBankCoreWriteSpecification := by proofs

theorem dram_bank_256x32_write_realizable :
    RealizableUnder (DramBankCoreWriteBehavior dramBank256x32Profile)
      (DramBankCoreWriteAllowed dramBank256x32Profile) := by proofs

theorem dram_bank_256x32_write_domain :
    StaysWithinValidityDomain
      (DramBankCoreWriteBehavior dramBank256x32Profile)
      (DramBankCoreWriteAllowed dramBank256x32Profile)
      DramBankCoreWriteDomain := by proofs

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
        (world.bits.bits row column) := by proofs

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
            row column) := by proofs

theorem dram_bank_256x32_write_assurance :
    AssuranceCase dramBank256x32
      (DramBankCoreWriteBehavior dramBank256x32Profile)
      (DramBankCoreWriteAllowed dramBank256x32Profile)
      dramBank256x32WriteSourceBinding
      DramBankCoreWriteSpecification DramBankCoreWriteDomain := by proofs

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
        DramBankCoreEndpointRepresents observation.restored after := by proofs

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
        DramBankCoreEndpointRepresents observation.after after := by proofs

#print axioms dram_bank_256x32_nominal_profile
#print axioms dram_bank_256x32_read_equation_manifest
#print axioms dram_bank_256x32_write_equation_manifest
#print axioms dram_bank_256x32_coupling_instance_projection
#print axioms dram_bank_256x32_coupling_equation_manifest
#print axioms dram_bank_256x32_coupling_initial_direction
#print axioms dram_bank_256x32_coupling_residual_realizable
#print axioms dram_bank_256x32_coupling_conserves_voltage_sums
#print axioms dram_bank_256x32_coupling_allowed
#print axioms dram_bank_256x32_coupling_transient_realizable
#print axioms dram_bank_256x32_coupling_transient_stays_in_domain
#print axioms dram_bank_256x32_coupling_establishes_ready
#print axioms dram_bank_256x32_coupled_regeneration_after_positive_time
#print axioms dram_bank_256x32_coupled_latch_realizable
#print axioms dram_bank_256x32_coupled_latch_margin_realizable
#print axioms dram_bank_256x32_coupled_latch_resolves
#print axioms dram_bank_256x32_parameter_projection
#print axioms dram_bank_256x32_topology_projection
#print axioms dram_bank_256x32_projection
#print axioms dram_bank_256x32_read_safe
#print axioms dram_bank_256x32_read_realizable
#print axioms dram_bank_256x32_read_domain
#print axioms dram_bank_256x32_precharge_derived
#print axioms dram_bank_256x32_reference_margin
#print axioms dram_bank_256x32_sense_local_regeneration
#print axioms dram_bank_256x32_sense_residual_realizable
#print axioms dram_bank_256x32_unselected_derived
#print axioms dram_bank_256x32_read_correct
#print axioms dram_bank_256x32_read_assurance
#print axioms dram_bank_256x32_write_safe
#print axioms dram_bank_256x32_write_realizable
#print axioms dram_bank_256x32_write_domain
#print axioms dram_bank_256x32_write_unselected_derived
#print axioms dram_bank_256x32_write_correct
#print axioms dram_bank_256x32_write_assurance
#print axioms dram_bank_256x32_read_refines_step
#print axioms dram_bank_256x32_write_refines_step
