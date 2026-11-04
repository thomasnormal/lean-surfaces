import LeanModels.Spice.DramBankPhysical
import LeanModels.Spice.DramBankCoreSpec
import LeanModels.Spice.DramBankSenseBridge
import LeanModels.Circuit.Surface
import LeanModels.Python.Surface

namespace Examples.spice.dram_bank_2x2.proof

open LeanModels.Circuit LeanModels.Spice

load_circuit dramBank2x2 from
  "Examples/spice/dram_bank_2x2/dram_bank_2x2.cir"

def dramBankLayout : DramBank2x2Layout :=
  match dramBank2x2.toDramBank2x2 with
  | .ok layout => layout
  | .error _ => default

/-- All 46 flattened devices, all three MOS models, and every named boundary port
match the checked complete-bank topology. -/
theorem dram_bank_2x2_projection :
    dramBank2x2.toDramBank2x2 = .ok checkedDramBank2x2Layout := by
  norm_num [LeanModels.Circuit.ElaboratedCircuit.toDramBank2x2,
    LeanModels.Spice.ElaboratedCircuit.toDramBank2x2,
    dramBank2x2TopologyMatches, dramBank2x2NamesMatch,
    matchesCapacitor, matchesMosfet, matchesMos1Model,
    LeanModels.Circuit.NodeId.beq_mk,
    LeanModels.Circuit.ModelId.beq_mk,
    dramBank2x2]

theorem dram_bank_2x2_projection_is_ok :
    (dramBank2x2.toDramBank2x2).isOk = true := by
  rw [dram_bank_2x2_projection]
  rfl

theorem dramBankLayout_eq :
    dramBankLayout = checkedDramBank2x2Layout := by
  unfold dramBankLayout
  rw [dram_bank_2x2_projection]

theorem dram_bank_2x2_layout :
    dramBank2x2.toDramBank2x2 = .ok dramBankLayout := by
  unfold dramBankLayout
  rw [dram_bank_2x2_projection]

/-- The public controls and observations are source-derived typed nodes, not
independently restated string names. -/
theorem dram_bank_2x2_typed_interface :
    dramBankLayout.supply = ⟨11⟩ ∧
    dramBankLayout.prechargeReference = ⟨8⟩ ∧
    dramBankLayout.activate = ⟨10⟩ ∧
    dramBankLayout.row = ⟨16⟩ ∧
    dramBankLayout.column = ⟨27⟩ ∧
    dramBankLayout.dataIn = ⟨28⟩ ∧
    dramBankLayout.dataOut = ⟨26⟩ := by
  rw [dramBankLayout_eq]
  norm_num [checkedDramBank2x2Layout]

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
        3 / 10000000000000) := by
  rw [dramBankLayout_eq]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro row column
    fin_cases row <;> fin_cases column <;>
      norm_num [checkedDramBank2x2Layout, selectFin2]
  · intro column
    fin_cases column <;>
      norm_num [checkedDramBank2x2Layout, selectFin2]

theorem dram_bank_2x2_nominal_profile :
    DramBank2x2FullProfile dramBankLayout := by
  constructor
  · intro row column
    rw [dramBankLayout_eq]
    fin_cases row <;> fin_cases column <;>
      norm_num [DramBank2x2NominalProfile,
        DramArrayLayout.cellInstance,
        checkedDramBank2x2Layout, selectFin2]
  · rw [dramBankLayout_eq]
    norm_num [DramBank2x2PeripheralProfile,
      checkedDramBank2x2Layout]

noncomputable def dramBank2x2CoreProfile : DramBankCoreProfile 2 2 :=
  { cells := dramBankLayout.array.cellInstance
    pThreshold := dramBankLayout.pThreshold
    pBeta := dramBankLayout.pBeta
    sensePThreshold := dramBankLayout.sensePThreshold
    sensePBeta := dramBankLayout.sensePBeta }

theorem dram_bank_2x2_core_nominal_profile :
    DramBankCoreNominalProfile dramBank2x2CoreProfile := by
  rcases dram_bank_2x2_nominal_profile with ⟨hcells, hperiphery⟩
  refine ⟨?_, ?_⟩
  · intro row column
    simpa [dramBank2x2CoreProfile, nominalDramCellInstance] using
      hcells row column
  · simp only [dramBank2x2CoreProfile]
    rw [dramBankLayout_eq]
    norm_num [dramBank2x2CoreProfile, checkedDramBank2x2Layout]

theorem dram_bank_2x2_read_equation_manifest :
    EquationManifest
      (DramBankCoreReadProgram dramBank2x2CoreProfile)
      ["legacy two-inverter sense endpoint contract"] :=
  dramBankCoreReadEquationManifest

theorem dram_bank_2x2_write_equation_manifest :
    EquationManifest
      (DramBankCoreWriteProgram dramBank2x2CoreProfile)
      ["read endpoint phase"] :=
  dramBankCoreWriteEquationManifest

noncomputable def dramBank2x2SourceBinding :
    SourceBinding dramBank2x2
      (DramBankCoreReadBehavior dramBank2x2CoreProfile)
      (DramBankCoreReadAllowed dramBank2x2CoreProfile) :=
  SourceBinding.checked
    LeanModels.Spice.ElaboratedCircuit.toDramBank2x2
    dramBank2x2 dramBankLayout dram_bank_2x2_layout
    (fun layout =>
      DramBankCoreReadBehavior
        { cells := layout.array.cellInstance
          pThreshold := layout.pThreshold
          pBeta := layout.pBeta
          sensePThreshold := layout.sensePThreshold
          sensePBeta := layout.sensePBeta })
    (fun layout =>
      DramBankCoreReadAllowed
        { cells := layout.array.cellInstance
          pThreshold := layout.pThreshold
          pBeta := layout.pBeta
          sensePThreshold := layout.sensePThreshold
          sensePBeta := layout.sensePBeta })

theorem dram_bank_2x2_read_safe :
    SafeUnder (DramBankCoreReadBehavior dramBank2x2CoreProfile)
      (DramBankCoreReadAllowed dramBank2x2CoreProfile)
      DramBankCoreReadSpecification :=
  LeanModels.Spice.dramBankCore_read_safe dramBank2x2CoreProfile

theorem dram_bank_2x2_read_realizable :
    RealizableUnder (DramBankCoreReadBehavior dramBank2x2CoreProfile)
      (DramBankCoreReadAllowed dramBank2x2CoreProfile) :=
  LeanModels.Spice.dramBankCore_read_realizable dramBank2x2CoreProfile

theorem dram_bank_2x2_read_domain :
    StaysWithinValidityDomain
      (DramBankCoreReadBehavior dramBank2x2CoreProfile)
      (DramBankCoreReadAllowed dramBank2x2CoreProfile)
      DramBankCoreReadDomain :=
  LeanModels.Spice.dramBankCore_read_domain dramBank2x2CoreProfile

/-- The finite-time bitline precharge band is derived from the enabled MOS1,
the 300 fF bitline capacitor, and their continuous DAE. -/
theorem dram_bank_2x2_precharge_derived
    {world : DramBankCoreReadWorld 2 2}
    {observation : DramBankCoreReadObservation 2 2}
    (hbehavior :
      DramBankCoreReadBehavior
        dramBank2x2CoreProfile world observation ()) :
    ∀ column,
      247 / 100 ≤ observation.prechargedBitline column ∧
        observation.prechargedBitline column ≤ 5 / 2 :=
  hbehavior.precharged_voltage_bounds
    dram_bank_2x2_core_nominal_profile

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
          observation.prechargedBitline column :=
  hbehavior.activated_reference_margin
    dram_bank_2x2_core_nominal_profile

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
      derivative .trueLine - derivative .complementLine < 0 :=
  hbehavior.differential_sense_local_regeneration
    dram_bank_2x2_core_nominal_profile hsupply hinstance column hresidual

/-- The composed pointwise latch premise is inhabited for the same source
bank observation and any nominal latch instance. -/
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
        derivative := by
  apply dramBankDifferentialSense_initial_residual_realizable
  · rw [hinstance]
    norm_num [nominalDramDifferentialSenseInstance]
  · rw [hinstance]
    norm_num [nominalDramDifferentialSenseInstance]

/-- The deselected row follows the source-parameterized 1T1C hold DAE.
Preservation is derived from that trajectory and endpoint wiring. -/
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
            (world.bits.bits otherRow column) := by
  intro otherRow hother column
  simpa [dramBankCoreInitialEndpoint] using
    hbehavior.unselected_preserved otherRow hother column

/-- The selected cell is reported and every restored cell remains in the
voltage band representing its stored bit. The selected-row endpoints are
derived from the finite-horizon restore DAE. -/
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
          (world.bits.bits row column) := by
  exact dram_bank_2x2_read_safe world observation ()
    dram_bank_2x2_core_nominal_profile hbehavior

theorem dram_bank_2x2_read_assurance :
    AssuranceCase dramBank2x2
      (DramBankCoreReadBehavior dramBank2x2CoreProfile)
      (DramBankCoreReadAllowed dramBank2x2CoreProfile)
      dramBank2x2SourceBinding
      DramBankCoreReadSpecification DramBankCoreReadDomain :=
  ⟨dram_bank_2x2_read_safe, dram_bank_2x2_read_realizable,
    dram_bank_2x2_read_domain⟩

noncomputable def dramBank2x2WriteSourceBinding :
    SourceBinding dramBank2x2
      (DramBankCoreWriteBehavior dramBank2x2CoreProfile)
      (DramBankCoreWriteAllowed dramBank2x2CoreProfile) :=
  SourceBinding.checked
    LeanModels.Spice.ElaboratedCircuit.toDramBank2x2
    dramBank2x2 dramBankLayout dram_bank_2x2_layout
    (fun layout =>
      DramBankCoreWriteBehavior
        { cells := layout.array.cellInstance
          pThreshold := layout.pThreshold
          pBeta := layout.pBeta
          sensePThreshold := layout.sensePThreshold
          sensePBeta := layout.sensePBeta })
    (fun layout =>
      DramBankCoreWriteAllowed
        { cells := layout.array.cellInstance
          pThreshold := layout.pThreshold
          pBeta := layout.pBeta
          sensePThreshold := layout.sensePThreshold
          sensePBeta := layout.sensePBeta })

theorem dram_bank_2x2_write_safe :
    SafeUnder (DramBankCoreWriteBehavior dramBank2x2CoreProfile)
      (DramBankCoreWriteAllowed dramBank2x2CoreProfile)
      DramBankCoreWriteSpecification :=
  LeanModels.Spice.dramBankCore_write_safe dramBank2x2CoreProfile

theorem dram_bank_2x2_write_realizable :
    RealizableUnder (DramBankCoreWriteBehavior dramBank2x2CoreProfile)
      (DramBankCoreWriteAllowed dramBank2x2CoreProfile) :=
  LeanModels.Spice.dramBankCore_write_realizable dramBank2x2CoreProfile

theorem dram_bank_2x2_write_domain :
    StaysWithinValidityDomain
      (DramBankCoreWriteBehavior dramBank2x2CoreProfile)
      (DramBankCoreWriteAllowed dramBank2x2CoreProfile)
      DramBankCoreWriteDomain :=
  LeanModels.Spice.dramBankCore_write_domain dramBank2x2CoreProfile

/-- Every cell outside the selected address continues to represent its prior
bit. Unselected rows are exactly preserved by cutoff hold; selected-row cells
on other columns continue their sense-clamped restore trajectories. -/
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
        (world.bits.bits row column) := by
  intro row column hother
  have hsafe := dram_bank_2x2_write_safe world observation ()
    dram_bank_2x2_core_nominal_profile hbehavior row column
  rw [DramMatrixState.write_other _ _ _ _ _ _ hother] at hsafe
  exact hsafe

/-- The selected cell follows the projected transient DAE into its logic
band; unselected wordlines and selected-row column isolation are also
DAE-derived. -/
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
            row column) := by
  exact dram_bank_2x2_write_safe world observation ()
    dram_bank_2x2_core_nominal_profile hbehavior

theorem dram_bank_2x2_write_assurance :
    AssuranceCase dramBank2x2
      (DramBankCoreWriteBehavior dramBank2x2CoreProfile)
      (DramBankCoreWriteAllowed dramBank2x2CoreProfile)
      dramBank2x2WriteSourceBinding
      DramBankCoreWriteSpecification DramBankCoreWriteDomain :=
  ⟨dram_bank_2x2_write_safe, dram_bank_2x2_write_realizable,
    dram_bank_2x2_write_domain⟩

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
        DramBankCoreEndpointRepresents observation.restored after :=
  LeanModels.Spice.dramBankCore_read_refines_step
    dram_bank_2x2_core_nominal_profile hbehavior

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
        DramBankCoreEndpointRepresents observation.after after :=
  LeanModels.Spice.dramBankCore_write_refines_step
    dram_bank_2x2_core_nominal_profile hbehavior

#equation_guard DramBankCoreReadProgram forbids
  [DramBankCoreReadSpecification, DramBankCoreWriteSpecification]

#equation_guard DramPrechargeProgram forbids
  [DramBankCoreReadSpecification, DramBankCoreWriteSpecification]

#equation_guard DramBankCoreWriteProgram forbids
  [DramBankCoreReadSpecification, DramBankCoreWriteSpecification]

#assurance_report dramBank2x2 using dram_bank_2x2_read_assurance
  [dram_bank_2x2_read_equation_manifest,
    dram_bank_2x2_precharge_derived,
    dram_bank_2x2_reference_margin,
    dram_bank_2x2_sense_local_regeneration,
    dram_bank_2x2_sense_residual_realizable,
    dram_bank_2x2_unselected_derived,
    dram_bank_2x2_read_correct, dram_bank_2x2_read_refines_step]

#assurance_report dramBank2x2 using dram_bank_2x2_write_assurance
  [dram_bank_2x2_write_equation_manifest,
    dram_bank_2x2_write_unselected_derived,
    dram_bank_2x2_write_correct, dram_bank_2x2_write_refines_step]

#equation_report dram_bank_2x2_read_equation_manifest
#equation_report dramPrechargeEquationManifest
#equation_report dram_bank_2x2_write_equation_manifest

#print axioms dram_bank_2x2_reference_margin
#print axioms dram_bank_2x2_sense_local_regeneration
#print axioms dram_bank_2x2_sense_residual_realizable

end Examples.spice.dram_bank_2x2.proof
