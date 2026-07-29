import Examples.spice.dram_bank_2x2.proof

open LeanModels.Circuit LeanModels.Spice
open Examples.spice.dram_bank_2x2.proof

theorem dram_bank_2x2_projection :
    dramBank2x2.toDramBank2x2 = .ok checkedDramBank2x2Layout := by proofs

theorem dram_bank_2x2_projection_is_ok :
    (dramBank2x2.toDramBank2x2).isOk = true := by proofs

theorem dram_bank_2x2_layout :
    dramBank2x2.toDramBank2x2 = .ok dramBankLayout := by proofs

theorem dram_bank_2x2_typed_interface :
    dramBankLayout.supply = ⟨11⟩ ∧
    dramBankLayout.prechargeReference = ⟨8⟩ ∧
    dramBankLayout.activate = ⟨10⟩ ∧
    dramBankLayout.row = ⟨16⟩ ∧
    dramBankLayout.column = ⟨27⟩ ∧
    dramBankLayout.dataIn = ⟨28⟩ ∧
    dramBankLayout.dataOut = ⟨26⟩ := by proofs

theorem dram_bank_2x2_device_profile :
    dramBankLayout.array.threshold = 1 ∧
    dramBankLayout.array.beta = 1 / 10000 ∧
    dramBankLayout.pThreshold = 1 ∧
    dramBankLayout.pBeta = 1 / 20000 ∧
    dramBankLayout.sensePThreshold = 1 ∧
    dramBankLayout.sensePBeta = 1 / 10000 ∧
    (∀ row column,
      (dramBankLayout.array.cells row column).storageCapacitance =
        3 / 100000000000000) ∧
    (∀ column,
      dramBankLayout.array.bitlineCapacitances column =
        3 / 10000000000000) := by proofs

theorem dram_bank_2x2_nominal_profile :
    DramBank2x2FullProfile dramBankLayout := by proofs

theorem dram_bank_2x2_core_nominal_profile :
    DramBankCoreNominalProfile dramBank2x2CoreProfile := by proofs

theorem dram_bank_2x2_read_equation_manifest :
    EquationManifest
      (DramBankCoreReadProgram dramBank2x2CoreProfile)
      ["legacy two-inverter sense endpoint contract"] := by proofs

theorem dram_bank_2x2_write_equation_manifest :
    EquationManifest
      (DramBankCoreWriteProgram dramBank2x2CoreProfile)
      ["read endpoint phase"] := by proofs

theorem dram_bank_2x2_read_safe :
    SafeUnder (DramBankCoreReadBehavior dramBank2x2CoreProfile)
      (DramBankCoreReadAllowed dramBank2x2CoreProfile)
      DramBankCoreReadSpecification := by proofs

theorem dram_bank_2x2_read_realizable :
    RealizableUnder (DramBankCoreReadBehavior dramBank2x2CoreProfile)
      (DramBankCoreReadAllowed dramBank2x2CoreProfile) := by proofs

theorem dram_bank_2x2_read_domain :
    StaysWithinValidityDomain
      (DramBankCoreReadBehavior dramBank2x2CoreProfile)
      (DramBankCoreReadAllowed dramBank2x2CoreProfile)
      DramBankCoreReadDomain := by proofs

theorem dram_bank_2x2_precharge_derived
    {world : DramBankCoreReadWorld 2 2}
    {observation : DramBankCoreReadObservation 2 2}
    (hbehavior :
      DramBankCoreReadBehavior
        dramBank2x2CoreProfile world observation ()) :
    ∀ column,
      247 / 100 ≤ observation.prechargedBitline column ∧
        observation.prechargedBitline column ≤ 5 / 2 := by proofs

/-- Charge sharing delivers at least `3/22 V` against an otherwise
precharged reference bitline, in the correct direction for either bit. -/
theorem dram_bank_2x2_reference_margin
    {world : DramBankCoreReadWorld 2 2}
    {observation : DramBankCoreReadObservation 2 2}
    (hbehavior :
      DramBankCoreReadBehavior
        dramBank2x2CoreProfile world observation ()) :
    ∀ column,
      if world.bits.bits world.row column then
        observation.prechargedBitline column + 3 / 22 ≤
          observation.activated.bitline column
      else
        observation.activated.bitline column + 3 / 22 ≤
          observation.prechargedBitline column := by proofs

/-- Once connected to a nominal differential latch with the selected
bitline as `trueLine` and a precharged reference as `complementLine`, the
source-derived bank endpoint is locally regenerative in the stored bit's
direction. The literal 2x2 deck does not yet instantiate that connection. -/
theorem dram_bank_2x2_sense_local_regeneration
    {bankWorld : DramBankCoreReadWorld 2 2}
    {observation : DramBankCoreReadObservation 2 2}
    {senseWorld : DramDifferentialSenseWorld}
    {time : ℝ}
    {derivative : VectorState DramDifferentialSenseIndex}
    (hbehavior :
      DramBankCoreReadBehavior
        dramBank2x2CoreProfile bankWorld observation ())
    (hsupply : senseWorld.environment.supply = 5)
    (hinstance :
      senseWorld.fabricated = nominalDramDifferentialSenseInstance)
    (column : Fin 2)
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

theorem dram_bank_2x2_sense_residual_realizable
    {bankWorld : DramBankCoreReadWorld 2 2}
    {observation : DramBankCoreReadObservation 2 2}
    {senseWorld : DramDifferentialSenseWorld}
    {time : ℝ}
    (_hbehavior :
      DramBankCoreReadBehavior
        dramBank2x2CoreProfile bankWorld observation ())
    (hinstance :
      senseWorld.fabricated = nominalDramDifferentialSenseInstance)
    (column : Fin 2) :
    ∃ derivative : VectorState DramDifferentialSenseIndex,
      dramDifferentialSenseDAE.residual senseWorld time
        (dramBankDifferentialSenseInitialState
          (observation.activated.bitline column)
          (observation.prechargedBitline column))
        derivative := by proofs

theorem dram_bank_2x2_unselected_derived
    {world : DramBankCoreReadWorld 2 2}
    {observation : DramBankCoreReadObservation 2 2}
    (hbehavior :
      DramBankCoreReadBehavior
        dramBank2x2CoreProfile world observation ()) :
    ∀ otherRow, otherRow ≠ world.row →
      ∀ column,
        observation.restored.storage otherRow column =
          dramBankCoreStoredVoltage
            (world.bits.bits otherRow column) := by proofs

theorem dram_bank_2x2_read_correct
    {world : DramBankCoreReadWorld 2 2}
    {observation : DramBankCoreReadObservation 2 2}
    (hbehavior :
      DramBankCoreReadBehavior
        dramBank2x2CoreProfile world observation ()) :
    observation.dataOut =
        logicVoltage (world.bits.bits world.row world.column) ∧
      ∀ row column,
        DramBankCoreStorageRepresents
          (observation.restored.storage row column)
          (world.bits.bits row column) := by proofs

theorem dram_bank_2x2_read_assurance :
    AssuranceCase dramBank2x2
      (DramBankCoreReadBehavior dramBank2x2CoreProfile)
      (DramBankCoreReadAllowed dramBank2x2CoreProfile)
      dramBank2x2SourceBinding
      DramBankCoreReadSpecification DramBankCoreReadDomain := by proofs

theorem dram_bank_2x2_write_safe :
    SafeUnder (DramBankCoreWriteBehavior dramBank2x2CoreProfile)
      (DramBankCoreWriteAllowed dramBank2x2CoreProfile)
      DramBankCoreWriteSpecification := by proofs

theorem dram_bank_2x2_write_realizable :
    RealizableUnder (DramBankCoreWriteBehavior dramBank2x2CoreProfile)
      (DramBankCoreWriteAllowed dramBank2x2CoreProfile) := by proofs

theorem dram_bank_2x2_write_domain :
    StaysWithinValidityDomain
      (DramBankCoreWriteBehavior dramBank2x2CoreProfile)
      (DramBankCoreWriteAllowed dramBank2x2CoreProfile)
      DramBankCoreWriteDomain := by proofs

theorem dram_bank_2x2_write_unselected_derived
    {world : DramBankCoreWriteWorld 2 2}
    {observation : DramBankCoreWriteObservation 2 2}
    (hbehavior :
      DramBankCoreWriteBehavior
        dramBank2x2CoreProfile world observation ()) :
    ∀ row column,
      row ≠ world.row ∨ column ≠ world.column →
      DramBankCoreStorageRepresents
        (observation.after.storage row column)
        (world.bits.bits row column) := by proofs

theorem dram_bank_2x2_write_correct
    {world : DramBankCoreWriteWorld 2 2}
    {observation : DramBankCoreWriteObservation 2 2}
    (hbehavior :
      DramBankCoreWriteBehavior
        dramBank2x2CoreProfile world observation ()) :
    ∀ row column,
      DramBankCoreStorageRepresents
        (observation.after.storage row column)
          ((world.bits.write world.row world.column world.value).bits
            row column) := by proofs

theorem dram_bank_2x2_write_assurance :
    AssuranceCase dramBank2x2
      (DramBankCoreWriteBehavior dramBank2x2CoreProfile)
      (DramBankCoreWriteAllowed dramBank2x2CoreProfile)
      dramBank2x2WriteSourceBinding
      DramBankCoreWriteSpecification DramBankCoreWriteDomain := by proofs

theorem dram_bank_2x2_read_refines_step
    {world : DramBankCoreReadWorld 2 2}
    {observation : DramBankCoreReadObservation 2 2}
    (hbehavior :
      DramBankCoreReadBehavior
        dramBank2x2CoreProfile world observation ()) :
    ∃ response after,
      DramBankStep world.bits
          (.read world.row world.column) response after ∧
        DramBankCoreReadResponseObserved observation response ∧
        DramBankCoreEndpointRepresents observation.restored after := by proofs

theorem dram_bank_2x2_write_refines_step
    {world : DramBankCoreWriteWorld 2 2}
    {observation : DramBankCoreWriteObservation 2 2}
    (hbehavior :
      DramBankCoreWriteBehavior
        dramBank2x2CoreProfile world observation ()) :
    ∃ after,
      DramBankStep world.bits
          (.write world.row world.column world.value)
          .acknowledged after ∧
        DramBankCoreEndpointRepresents observation.after after := by proofs

#print axioms dram_bank_2x2_projection
#print axioms dram_bank_2x2_projection_is_ok
#print axioms dram_bank_2x2_layout
#print axioms dram_bank_2x2_typed_interface
#print axioms dram_bank_2x2_device_profile
#print axioms dram_bank_2x2_nominal_profile
#print axioms dram_bank_2x2_core_nominal_profile
#print axioms dramPrechargeProgram_physicsOnly
#print axioms dramPrechargeEquationManifest
#print axioms nominalDramPrecharge_behavior_zero_ten_ns_settles
#print axioms dram_bank_2x2_read_equation_manifest
#print axioms dram_bank_2x2_write_equation_manifest
#print axioms dram_bank_2x2_read_safe
#print axioms dram_bank_2x2_read_realizable
#print axioms dram_bank_2x2_read_domain
#print axioms dram_bank_2x2_precharge_derived
#print axioms dram_bank_2x2_reference_margin
#print axioms dram_bank_2x2_sense_local_regeneration
#print axioms dram_bank_2x2_sense_residual_realizable
#print axioms dram_bank_2x2_unselected_derived
#print axioms dram_bank_2x2_read_correct
#print axioms dram_bank_2x2_read_assurance
#print axioms dram_bank_2x2_write_safe
#print axioms dram_bank_2x2_write_realizable
#print axioms dram_bank_2x2_write_domain
#print axioms dram_bank_2x2_write_unselected_derived
#print axioms dram_bank_2x2_write_correct
#print axioms dram_bank_2x2_write_assurance
#print axioms dram_bank_2x2_read_refines_step
#print axioms dram_bank_2x2_write_refines_step
