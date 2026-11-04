import LeanModels.Spice.DramBankCore
import LeanModels.Spice.Dram1T1CSpec
import LeanModels.Spice.DramWriteSpec

/-!
# DRAM endpoint specifications and refinement

This module deliberately imports the DRAM equation core, never the reverse.
The physical behavior in `DramBankCore` is therefore unable to depend on any
specification declared here. Imported endpoint contracts remain visible in
the core's `EquationManifest`; the theorems below only observe that behavior.
-/

namespace LeanModels.Spice

open LeanModels.Circuit Set

def DramBankCoreStorageRepresents (voltage : ℝ) (value : Bool) : Prop :=
  if value then
    3 ≤ voltage ∧ voltage ≤ 4
  else
    0 ≤ voltage ∧ voltage ≤ 1

theorem dramBankCoreStoredVoltage_represents (value : Bool) :
    DramBankCoreStorageRepresents
      (dramBankCoreStoredVoltage value) value := by
  cases value <;>
    norm_num [DramBankCoreStorageRepresents, dramBankCoreStoredVoltage]

/-- The write-zero decay constant.  This was seven bespoke lines until the F2
kit landed (`Circuit/Enclosure.lean`); it is now one application of the decay
certificate at split depth 1, and the same call discharges every other
constant of this shape. -/
theorem dramBankCore_exp_write_zero_bound :
    Real.exp (-(16 / 3 : ℝ)) ≤ 1 / 4 :=
  LeanModels.Circuit.exp_neg_le_of_pow_le (by norm_num) 1 (by norm_num)
    (by norm_num)

noncomputable def DramBankCoreReadSpecification
    (world : DramBankCoreReadWorld rows columns)
    (observation : DramBankCoreReadObservation rows columns)
    (_internal : Unit) : Prop :=
  observation.dataOut =
      logicVoltage (world.bits.bits world.row world.column) ∧
    ∀ row column,
      DramBankCoreStorageRepresents
        (observation.restored.storage row column)
        (world.bits.bits row column)

noncomputable def DramBankCoreReadDomain
    (_world : DramBankCoreReadWorld rows columns)
    (observation : DramBankCoreReadObservation rows columns)
    (_internal : Unit) : Prop :=
  (∀ column,
    0 ≤ observation.prechargedBitline column ∧
      observation.prechargedBitline column ≤ 5) ∧
  (∀ column,
    0 ≤ observation.activated.bitline column ∧
      observation.activated.bitline column ≤ 5) ∧
  (∀ column,
    0 ≤ observation.senseIntermediate column ∧
      observation.senseIntermediate column ≤ 5) ∧
  (∀ column,
    0 ≤ observation.senseOutput column ∧
      observation.senseOutput column ≤ 5) ∧
  0 ≤ observation.dataOut ∧ observation.dataOut ≤ 5 ∧
  ∀ row column,
    0 ≤ observation.restored.storage row column ∧
      observation.restored.storage row column ≤ 5

theorem DramBankCoreReadBehavior.restored_selected_storage_represents
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    {observation : DramBankCoreReadObservation rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (hbehavior :
      DramBankCoreReadBehavior profile world observation ()) :
    ∀ column,
      DramBankCoreStorageRepresents
        (observation.restored.storage world.row column)
        (world.bits.bits world.row column) := by
  intro column
  have hendpoint :=
    (hbehavior.restored_selected_cell hprofile column).1
  have hevolution := hbehavior .restoreEvolution column
  cases hbit : world.bits.bits world.row column
  · simp only [hbit, Bool.false_eq_true, ↓reduceIte,
      DramBankCoreStorageRepresents]
    rw [if_neg (by simpa using hbit)] at hevolution
    have hactivated :=
      hbehavior.activated_cell_voltage hprofile column
    rw [hbit] at hactivated
    simp only [Bool.false_eq_true, if_false] at hactivated
    have hinitial0 :
        0 ≤ observation.activated.storage world.row column := by
      rw [hactivated.1]
      linarith [hactivated.2.1]
    have hinitial5 :
        observation.activated.storage world.row column ≤ 5 := by
      rw [hactivated.1]
      linarith [hactivated.2.2]
    have hinitialUpper :
        observation.activated.storage world.row column ≤ 25 / 11 := by
      rw [hactivated.1]
      exact hactivated.2.2
    rw [dramBankCore_restore_zero_world_eq_nominal
      hprofile hbehavior column hbit] at hevolution
    have hrate :
        loadedInverterDecayRate
              (nominalDramBankCoreRestoreZeroWorld
                (observation.activated.storage
                  world.row column)).asLoadedInverter *
            dramBankCoreRestoreHorizon =
          16 / 3 := by
      norm_num [loadedInverterDecayRate, loadedInverterNOverdrive,
        Dram1T1CWorld.asLoadedInverter,
        nominalDramBankCoreRestoreZeroWorld,
        dramBankCoreRestoreHorizon, deterministicWorld]
    have hdeadline :
        (nominalDramBankCoreRestoreZeroWorld
            (observation.activated.storage
              world.row column)).environment.initialVoltage *
            Real.exp
              (-loadedInverterDecayRate
                  (nominalDramBankCoreRestoreZeroWorld
                    (observation.activated.storage
                      world.row column)).asLoadedInverter *
                dramBankCoreRestoreHorizon) ≤
          1 := by
      rw [show
        -loadedInverterDecayRate
              (nominalDramBankCoreRestoreZeroWorld
                (observation.activated.storage
                  world.row column)).asLoadedInverter *
            dramBankCoreRestoreHorizon =
          -(16 / 3 : ℝ) by linarith]
      have hfirst :=
        mul_le_mul_of_nonneg_left
          dramBankCore_exp_write_zero_bound
          hinitial0
      have hsecond :=
        mul_le_mul_of_nonneg_right hinitialUpper
          (show (0 : ℝ) ≤ 1 / 4 by norm_num)
      simpa [nominalDramBankCoreRestoreZeroWorld,
        deterministicWorld] using hfirst.trans
          (hsecond.trans (show (25 / 11 : ℝ) * (1 / 4) ≤ 1 by norm_num))
    have hsettles :=
      dram1T1C_write_zero_settles
        (nominalDramBankCoreRestoreZeroWorld_admissible
          hinitial0 hinitial5) rfl
        hevolution (show (0 : ℝ) ≤ 1 by norm_num)
        (show (0 : ℝ) ≤ dramBankCoreRestoreHorizon by
          norm_num [dramBankCoreRestoreHorizon])
        le_rfl hdeadline
    have herror :=
      hsettles.2.2.2 dramBankCoreRestoreHorizon le_rfl le_rfl
    have hbounds :=
      hbehavior.restored_selected_storage_bounds hprofile column
    rw [hendpoint]
    constructor
    · simpa [hendpoint] using hbounds.1
    · have hnonneg :
          0 ≤ observation.selectedRestoreTrace column
            dramBankCoreRestoreHorizon := by
        simpa [hendpoint] using hbounds.1
      simpa [sub_zero, abs_of_nonneg hnonneg] using herror
  · simp only [hbit, ↓reduceIte, DramBankCoreStorageRepresents]
    rw [if_pos hbit] at hevolution
    have hactivated :=
      hbehavior.activated_cell_voltage hprofile column
    rw [hbit] at hactivated
    simp only [if_true] at hactivated
    have hinitial4 :
        observation.activated.storage world.row column ≤ 4 := by
      rw [hactivated.1]
      linarith [hactivated.2.2]
    rw [dramBankCore_restore_one_world_eq_nominal
      hprofile hbehavior column hbit] at hevolution
    have hsettles :=
      nominalDramWriteOne_settles_within
        (initialStorage :=
          observation.activated.storage world.row column)
        (horizon := dramBankCoreRestoreHorizon)
        (boundary := ⟨observation.selectedRestoreTrace column⟩)
        hinitial4
        (by norm_num [dramBankCoreRestoreHorizon])
        hevolution
        (show (0 : ℝ) ≤ 1 by norm_num)
        (show (0 : ℝ) ≤ dramBankCoreRestoreHorizon by
          norm_num [dramBankCoreRestoreHorizon])
        le_rfl
        (by
          have hdenominator :=
            nominalDramWriteOneTrace_denominator_pos
              (initialStorage :=
                observation.activated.storage world.row column)
              (time := dramBankCoreRestoreHorizon)
              hinitial4
              (by norm_num [dramBankCoreRestoreHorizon])
          rw [div_le_iff₀ hdenominator]
          norm_num [nominalDramWriteOneRate,
            dramBankCoreRestoreHorizon]
          nlinarith)
    have herror :=
      hsettles.2.2.2 dramBankCoreRestoreHorizon le_rfl le_rfl
    have hbounds :=
      hbehavior.restored_selected_storage_bounds hprofile column
    rw [hendpoint]
    rw [abs_le] at herror
    exact ⟨by linarith, by simpa [hendpoint] using hbounds.2⟩

theorem dramBankCore_read_safe
    (profile : DramBankCoreProfile rows columns) :
    SafeUnder (DramBankCoreReadBehavior profile)
      (DramBankCoreReadAllowed profile)
      DramBankCoreReadSpecification := by
  intro world observation _internal hprofile hbehavior
  have hsense := hbehavior.sense_correct hprofile
  have hmux := hbehavior .readMuxConnection
  have hunselected := hbehavior.unselected_preserved
  constructor
  · exact (dramTransmissionGate_correct hmux).trans (hsense world.column)
  · intro row column
    by_cases hrow : row = world.row
    · subst row
      exact hbehavior.restored_selected_storage_represents
        hprofile column
    · rw [hunselected row hrow column]
      exact dramBankCoreStoredVoltage_represents _

theorem dramBankCore_read_domain
    (profile : DramBankCoreProfile rows columns) :
    StaysWithinValidityDomain (DramBankCoreReadBehavior profile)
      (DramBankCoreReadAllowed profile) DramBankCoreReadDomain := by
  intro world observation _internal hprofile hbehavior
  have hsafe := dramBankCore_read_safe profile
    world observation () hprofile hbehavior
  have hsense := hbehavior.sense_correct hprofile
  have hsenseEquations := hbehavior .senseDevice
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro column
    have hprecharge :=
      hbehavior.precharged_voltage_bounds hprofile column
    constructor <;> linarith [hprecharge.1, hprecharge.2]
  · intro column
    have hactivated := hbehavior.activated_voltage hprofile column
    cases hbit : world.bits.bits world.row column
    · simp only [hbit, Bool.false_eq_true, if_false] at hactivated
      constructor <;> linarith [hactivated.1, hactivated.2]
    · simp only [hbit, if_true] at hactivated
      constructor <;> linarith [hactivated.1, hactivated.2]
  · intro column
    exact (hsenseEquations column).1.1
  · intro column
    rw [hsense column]
    cases world.bits.bits world.row column <;> simp [logicVoltage]
  · rw [hsafe.1]
    cases world.bits.bits world.row world.column <;> simp [logicVoltage]
  · rw [hsafe.1]
    cases world.bits.bits world.row world.column <;> simp [logicVoltage]
  · intro row column
    have hstorage := hsafe.2 row column
    unfold DramBankCoreStorageRepresents at hstorage
    split at hstorage
    · exact ⟨by linarith [hstorage.1], by linarith [hstorage.2]⟩
    · exact ⟨hstorage.1, by linarith [hstorage.2]⟩

theorem nominalDramBankCoreWriteZero_decay_rate
    (initialStorage : ℝ) :
    loadedInverterDecayRate
          (nominalDramBankCoreWriteZeroWorld initialStorage).asLoadedInverter *
        dramBankCoreWriteHorizon =
      16 / 3 := by
  norm_num [loadedInverterDecayRate, loadedInverterNOverdrive,
    Dram1T1CWorld.asLoadedInverter, nominalDramBankCoreWriteZeroWorld,
    dramBankCoreWriteHorizon, deterministicWorld]

theorem DramBankCoreWriteBehavior.unselected_column_storage_represents
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreWriteWorld rows columns}
    {observation : DramBankCoreWriteObservation rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (hbehavior :
      DramBankCoreWriteBehavior profile world observation ())
    (column : Fin columns) (hcolumn : column ≠ world.column) :
    DramBankCoreStorageRepresents
      (observation.after.storage world.row column)
      (world.bits.bits world.row column) := by
  have hreadBehavior := hbehavior .readEndpoint
  have hreadSafe := dramBankCore_read_safe profile
    world.readWorld observation.readPhase () hprofile hreadBehavior
  have hinitialRep := hreadSafe.2 world.row column
  simp only [DramBankCoreWriteWorld.readWorld] at hinitialRep
  have hevolution :=
    hbehavior .unselectedColumnEvolution column hcolumn
  have hendpoint :=
    hbehavior .unselectedColumnStorageEndpoint column hcolumn
  cases hbit : world.bits.bits world.row column
  · simp only [hbit, Bool.false_eq_true, ↓reduceIte,
      DramBankCoreStorageRepresents] at hinitialRep ⊢
    rw [if_neg (by simpa using hbit)] at hevolution
    rw [dramBankCore_unselected_column_zero_world_eq_nominal
      hprofile world observation.readPhase column] at hevolution
    have hadmissible :
        Dram1T1CAdmissible
          (nominalDramBankCoreWriteZeroWorld
            (observation.readPhase.restored.storage
              world.row column)) := by
      simp only [Dram1T1CAdmissible,
        nominalDramBankCoreWriteZeroWorld, deterministicWorld,
        dramBankCoreWriteHorizon]
      exact ⟨by norm_num, by norm_num, by norm_num, by norm_num,
        hinitialRep.1, by linarith [hinitialRep.2], by norm_num⟩
    have hloaded :
        LoadedInverterBehavior
          (nominalDramBankCoreWriteZeroWorld
            (observation.readPhase.restored.storage
              world.row column)).asLoadedInverter
          ⟨observation.unselectedColumnTrace column⟩ () := by
      simpa [Dram1T1CBehavior, Dram1T1CProgram,
        nominalDramBankCoreWriteZeroWorld,
        deterministicWorld] using hevolution .evolution
    have htime :
        dramBankCoreWriteHorizon ∈
          Icc (0 : ℝ) dramBankCoreWriteHorizon := by
      norm_num [dramBankCoreWriteHorizon]
    have hstart :
        observation.unselectedColumnTrace column
            dramBankCoreWriteHorizon ≤
          observation.unselectedColumnTrace column 0 :=
      loadedInverter_antitone_discharging
        hadmissible.asLoadedInverter rfl hloaded.2
        (by
          norm_num [nominalDramBankCoreWriteZeroWorld,
            Dram1T1CWorld.asLoadedInverter,
            dramBankCoreWriteHorizon, deterministicWorld])
        htime htime.1
    have hinitial :
        observation.unselectedColumnTrace column 0 =
          observation.readPhase.restored.storage world.row column := by
      simpa [nominalDramBankCoreWriteZeroWorld,
        Dram1T1CWorld.asLoadedInverter, deterministicWorld] using
          hloaded.2.1
    have hdomain :=
      loadedInverter_no_overshoot hadmissible.asLoadedInverter
        hloaded.2 dramBankCoreWriteHorizon htime
    rw [hendpoint]
    exact ⟨hdomain.1, by rw [hinitial] at hstart; linarith⟩
  · simp only [hbit, ↓reduceIte, DramBankCoreStorageRepresents]
      at hinitialRep ⊢
    rw [if_pos hbit] at hevolution
    rw [dramBankCore_unselected_column_one_world_eq_nominal
      hprofile world observation.readPhase hreadBehavior column hbit]
      at hevolution
    have hnoOvershoot :=
      nominalDramWriteOne_no_overshoot hinitialRep.2
        (show (0 : ℝ) ≤ dramBankCoreWriteHorizon by
          norm_num [dramBankCoreWriteHorizon])
        hevolution dramBankCoreWriteHorizon
        (by norm_num [dramBankCoreWriteHorizon]) le_rfl
    rw [hendpoint]
    exact ⟨hinitialRep.1.trans hnoOvershoot.1, hnoOvershoot.2⟩

noncomputable def DramBankCoreWriteSpecification
    (world : DramBankCoreWriteWorld rows columns)
    (observation : DramBankCoreWriteObservation rows columns)
    (_internal : Unit) : Prop :=
  ∀ row column,
    DramBankCoreStorageRepresents
      (observation.after.storage row column)
        ((world.bits.write world.row world.column world.value).bits
          row column)

noncomputable def DramBankCoreWriteDomain
    (_world : DramBankCoreWriteWorld rows columns)
    (observation : DramBankCoreWriteObservation rows columns)
    (_internal : Unit) : Prop :=
  0 ≤ observation.writeBus ∧ observation.writeBus ≤ 5 ∧
  (∀ column,
    0 ≤ observation.after.bitline column ∧
      observation.after.bitline column ≤ 5) ∧
  ∀ row column,
    0 ≤ observation.after.storage row column ∧
      observation.after.storage row column ≤ 5

theorem dramBankCore_write_safe
    (profile : DramBankCoreProfile rows columns) :
    SafeUnder (DramBankCoreWriteBehavior profile)
      (DramBankCoreWriteAllowed profile)
      DramBankCoreWriteSpecification := by
  intro world observation _internal hprofile hbehavior
  have hread := dramBankCore_read_safe profile
    world.readWorld observation.readPhase () hprofile
    (hbehavior .readEndpoint)
  have hreadBehavior := hbehavior .readEndpoint
  have hrestored :=
    hreadBehavior.restored_selected_cell hprofile world.column
  simp only [DramBankCoreWriteWorld.readWorld] at hrestored
  have hinitialRep := hread.2 world.row world.column
  simp only [DramBankCoreWriteWorld.readWorld] at hinitialRep
  have hinitial0 :
      0 ≤ observation.readPhase.restored.storage
        world.row world.column := by
    unfold DramBankCoreStorageRepresents at hinitialRep
    split at hinitialRep <;> linarith [hinitialRep.1]
  have hinitial4 :
      observation.readPhase.restored.storage
          world.row world.column ≤ 4 := by
    unfold DramBankCoreStorageRepresents at hinitialRep
    split at hinitialRep <;> linarith [hinitialRep.2]
  intro row column
  by_cases hselected :
      row = world.row ∧ column = world.column
  · rcases hselected with ⟨rfl, rfl⟩
    rw [DramMatrixState.write_selected]
    have hendpoint :
        observation.after.storage world.row world.column =
          observation.selectedStorageTrace dramBankCoreWriteHorizon := by
      simpa [DramBankCoreWriteProgram] using
        hbehavior .selectedStorageEndpoint
    cases hvalue : world.value
    · simp only [hvalue, Bool.false_eq_true, ↓reduceIte,
        DramBankCoreStorageRepresents]
      have hselected :
          Dram1T1CBehavior
            (dramBankCoreSelectedWriteZeroWorld
              profile world observation.readPhase)
            ⟨observation.selectedStorageTrace⟩ () := by
        simpa [DramBankCoreWriteProgram, hvalue] using
          hbehavior .selectedStorageEvolution
      rw [dramBankCore_selected_write_zero_world_eq_nominal
        hprofile world observation.readPhase] at hselected
      have hadmissible :
          Dram1T1CAdmissible
            (nominalDramBankCoreWriteZeroWorld
              (observation.readPhase.restored.storage
                world.row world.column)) := by
        simp only [Dram1T1CAdmissible,
          nominalDramBankCoreWriteZeroWorld, deterministicWorld,
          dramBankCoreWriteHorizon]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num,
          hinitial0, by linarith, by norm_num⟩
      have hrate :=
        nominalDramBankCoreWriteZero_decay_rate
          (observation.readPhase.restored.storage
            world.row world.column)
      have hdeadline :
          observation.readPhase.restored.storage world.row world.column *
              Real.exp
                (-loadedInverterDecayRate
                    (nominalDramBankCoreWriteZeroWorld
                      (observation.readPhase.restored.storage
                        world.row world.column)).asLoadedInverter *
                  dramBankCoreWriteHorizon) ≤
            1 := by
        rw [show
          -loadedInverterDecayRate
                (nominalDramBankCoreWriteZeroWorld
                  (observation.readPhase.restored.storage
                    world.row world.column)).asLoadedInverter *
              dramBankCoreWriteHorizon =
            -(16 / 3 : ℝ) by linarith]
        have hproduct :=
          mul_le_mul_of_nonneg_left
            dramBankCore_exp_write_zero_bound hinitial0
        nlinarith
      have hsettles :=
        dram1T1C_write_zero_settles hadmissible rfl hselected
          (show (0 : ℝ) ≤ 1 by norm_num)
          (show (0 : ℝ) ≤ dramBankCoreWriteHorizon by
            norm_num [dramBankCoreWriteHorizon])
          (show dramBankCoreWriteHorizon ≤
              (nominalDramBankCoreWriteZeroWorld
                (observation.readPhase.restored.storage
                  world.row world.column)).environment.horizon by rfl)
          hdeadline
      have herror :=
        hsettles.2.2.2 dramBankCoreWriteHorizon le_rfl le_rfl
      have hdomain :=
        dram1T1C_stays_in_domain
          (nominalDramBankCoreWriteZeroWorld
            (observation.readPhase.restored.storage
              world.row world.column))
          ⟨observation.selectedStorageTrace⟩ () hadmissible hselected
          dramBankCoreWriteHorizon
          (by norm_num [dramBankCoreWriteHorizon]) le_rfl
      rw [hendpoint]
      constructor
      · exact hdomain.1
      · simpa [sub_zero, abs_of_nonneg hdomain.1] using herror
    · simp only [hvalue, ↓reduceIte, DramBankCoreStorageRepresents]
      have hselected :
          DramWriteBehavior
            (dramBankCoreSelectedWriteOneWorld
              profile world observation.readPhase)
            ⟨observation.selectedStorageTrace⟩ () := by
        simpa [DramBankCoreWriteProgram, hvalue] using
          hbehavior .selectedStorageEvolution
      rw [dramBankCore_selected_write_one_world_eq_nominal
        hprofile world observation.readPhase] at hselected
      have hsettles :=
        nominalDramWriteOne_settles_within
          hinitial4
          (show (0 : ℝ) ≤ dramBankCoreWriteHorizon by
            norm_num [dramBankCoreWriteHorizon])
          hselected
          (show (0 : ℝ) ≤ 1 by norm_num)
          (show (0 : ℝ) ≤ dramBankCoreWriteHorizon by
            norm_num [dramBankCoreWriteHorizon])
          le_rfl
          (by
            have hdenominator :=
              nominalDramWriteOneTrace_denominator_pos
                hinitial4
                (show (0 : ℝ) ≤ dramBankCoreWriteHorizon by
                  norm_num [dramBankCoreWriteHorizon])
            rw [div_le_iff₀ hdenominator]
            norm_num [nominalDramWriteOneRate,
              dramBankCoreWriteHorizon]
            linarith)
      have herror :=
        hsettles.2.2.2 dramBankCoreWriteHorizon le_rfl le_rfl
      have hnoOvershoot :=
        nominalDramWriteOne_no_overshoot hinitial4
          (show (0 : ℝ) ≤ dramBankCoreWriteHorizon by
            norm_num [dramBankCoreWriteHorizon])
          hselected dramBankCoreWriteHorizon
          (by norm_num [dramBankCoreWriteHorizon]) le_rfl
      rw [hendpoint]
      rw [abs_le] at herror
      exact ⟨by linarith, hnoOvershoot.2⟩
  · have hother : row ≠ world.row ∨ column ≠ world.column :=
      not_and_or.mp hselected
    rw [DramMatrixState.write_other _ _ _ _ _ _ hother]
    by_cases hrow : row = world.row
    · subst row
      have hcolumn : column ≠ world.column := by
        intro hcolumn
        exact hselected ⟨rfl, hcolumn⟩
      exact hbehavior.unselected_column_storage_represents
        hprofile column hcolumn
    · rw [hbehavior.unselected_row_storage_preserved
        hprofile row column hrow]
      exact hread.2 row column

theorem dramBankCore_write_domain
    (profile : DramBankCoreProfile rows columns) :
    StaysWithinValidityDomain (DramBankCoreWriteBehavior profile)
      (DramBankCoreWriteAllowed profile)
      DramBankCoreWriteDomain := by
  intro world observation _internal hprofile hbehavior
  have hsafe := dramBankCore_write_safe profile
    world observation () hprofile hbehavior
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [dramTransmissionGate_correct
      (hbehavior .writeBusConnection)]
    cases world.value <;> simp [logicVoltage]
  · rw [dramTransmissionGate_correct
      (hbehavior .writeBusConnection)]
    cases world.value <;> simp [logicVoltage]
  · intro column
    by_cases hcolumn : column = world.column
    · subst column
      rw [dramTransmissionGate_correct
        (hbehavior .selectedBitlineConnection)]
      rw [dramTransmissionGate_correct
        (hbehavior .writeBusConnection)]
      cases world.value <;> simp [logicVoltage]
    · rw [hbehavior.unselected_bitline_preserved
        hprofile column hcolumn]
      have hreadDomain := dramBankCore_read_domain profile
        world.readWorld observation.readPhase () hprofile
        (hbehavior .readEndpoint)
      have hrestore :=
        hbehavior .readEndpoint .restoreConnection
      rw [dramTransmissionGate_correct (hrestore column)]
      exact hreadDomain.2.2.2.1 column
  · intro row column
    have hrepresents := hsafe row column
    unfold DramBankCoreStorageRepresents at hrepresents
    split at hrepresents
    · exact ⟨by linarith [hrepresents.1], by linarith [hrepresents.2]⟩
    · exact ⟨hrepresents.1, by linarith [hrepresents.2]⟩

noncomputable def DramBankCoreReadResponseObserved
    (observation : DramBankCoreReadObservation rows columns)
    (response : DramBankResponse) : Prop :=
  match response with
  | .readData value => observation.dataOut = logicVoltage value
  | .acknowledged => False

noncomputable def DramBankCoreEndpointRepresents
    (endpoint : DramArrayEndpoint rows columns)
    (state : DramMatrixState rows columns) : Prop :=
  ∀ row column,
    DramBankCoreStorageRepresents
      (endpoint.storage row column) (state.bits row column)

theorem dramBankCore_read_refines_step
    {profile : DramBankCoreProfile rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    {world : DramBankCoreReadWorld rows columns}
    {observation : DramBankCoreReadObservation rows columns}
    (hbehavior :
      DramBankCoreReadBehavior profile world observation ()) :
    ∃ response after,
      DramBankStep world.bits
          (.read world.row world.column) response after ∧
        DramBankCoreReadResponseObserved observation response ∧
        DramBankCoreEndpointRepresents observation.restored after := by
  have hsafe := dramBankCore_read_safe profile
    world observation () hprofile hbehavior
  refine ⟨.readData (world.bits.bits world.row world.column),
    world.bits, ?_, ?_, ?_⟩
  · simp [DramBankStep]
  · simpa [DramBankCoreReadResponseObserved] using hsafe.1
  · intro row column
    exact hsafe.2 row column

theorem dramBankCore_write_refines_step
    {profile : DramBankCoreProfile rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    {world : DramBankCoreWriteWorld rows columns}
    {observation : DramBankCoreWriteObservation rows columns}
    (hbehavior :
      DramBankCoreWriteBehavior profile world observation ()) :
    ∃ after,
      DramBankStep world.bits
          (.write world.row world.column world.value)
          .acknowledged after ∧
        DramBankCoreEndpointRepresents observation.after after := by
  have hsafe := dramBankCore_write_safe profile
    world observation () hprofile hbehavior
  refine ⟨world.bits.write world.row world.column world.value, ?_, ?_⟩
  · simp [DramBankStep]
  · exact hsafe

end LeanModels.Spice
