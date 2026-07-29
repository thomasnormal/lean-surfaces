import LeanModels.Spice.DramPeriphery
import LeanModels.Spice.Dram1T1C
import LeanModels.Spice.DramCell
import LeanModels.Spice.DramWrite
import LeanModels.Circuit.Equation

/-!
# Dimension-generic DRAM endpoint-contract core

The bank core composes source-derived 1T1C cells with precharge, MOS1 sense,
restore, and column transmission-gate contracts. Row and column controls are
one-hot boundary excitations; binary address decoding is intentionally outside
this component.

The result is a source-validated compositional endpoint-contract prototype.
Charge sharing, unselected-cell preservation, and the stated device/KCL
equations are derived, and the relation is proved realizable and
domain-bounded. Selected restore and write endpoints are values of
source-derived finite-horizon MOS1/capacitor trajectories, not behavior
premises.
The generic endpoint theorem still imports a legacy two-inverter sense
contract over conservative low/high input bands. That dependency is tagged as
an imported contract in the equation manifest; it is not presented as a
primitive law of a differential-latch deck. Source-projected differential
sensing and its local DAE theorems live in `DramDifferentialSense` and
`DramBankSenseBridge`. The finite coupling/sense trajectory remains the
refinement needed to remove this legacy clause.
-/

namespace LeanModels.Spice

open LeanModels.Circuit Set

structure DramBankCoreProfile (rows columns : Nat) where
  cells : Fin rows → Fin columns → DramCellInstance
  pThreshold : ℝ
  pBeta : ℝ
  sensePThreshold : ℝ
  sensePBeta : ℝ

noncomputable def nominalDramCellInstance : DramCellInstance :=
  { threshold := 1
    beta := 1 / 10000
    storageCapacitance := 3 / 100000000000000
    bitlineCapacitance := 3 / 10000000000000 }

noncomputable def DramBankCoreNominalProfile
    (profile : DramBankCoreProfile rows columns) : Prop :=
  (∀ row column, profile.cells row column = nominalDramCellInstance) ∧
    profile.pThreshold = 1 ∧
    profile.pBeta = 1 / 20000 ∧
    profile.sensePThreshold = 1 ∧
    profile.sensePBeta = 1 / 10000

structure DramBankCoreReadWorld (rows columns : Nat) where
  bits : DramMatrixState rows columns
  row : Fin rows
  column : Fin columns

structure DramBankCoreReadObservation (rows columns : Nat) where
  prechargeTrace : Fin columns → DenseTrace ℝ
  prechargedBitline : Fin columns → ℝ
  activated : DramArrayEndpoint rows columns
  senseIntermediate : Fin columns → ℝ
  senseOutput : Fin columns → ℝ
  dataOut : ℝ
  selectedRestoreTrace : Fin columns → DenseTrace ℝ
  unselectedStorageTrace : Fin rows → Fin columns → DenseTrace ℝ
  restored : DramArrayEndpoint rows columns

noncomputable def dramBankCoreStoredVoltage (stored : Bool) : ℝ :=
  if stored then 4 else 0

noncomputable def dramBankCoreRestoreHorizon : ℝ :=
  1 / 1000000000

/-- Source-derived precharge world for one bank column.  The selected row is
used only to recover the column capacitance from the uniform typed profile; the
nominal-profile theorem below proves that this choice is immaterial. -/
noncomputable def dramBankCorePrechargeWorld
    (profile : DramBankCoreProfile rows columns)
    (world : DramBankCoreReadWorld rows columns)
    (column : Fin columns) : DramPrechargeWorld :=
  deterministicWorld
    { threshold := (profile.cells world.row column).threshold
      beta := (profile.cells world.row column).beta
      bitlineCapacitance :=
        (profile.cells world.row column).bitlineCapacitance }
    { gateVoltage := 5
      referenceVoltage := 5 / 2
      initialVoltage := 0
      horizon := dramBankPrechargeHorizon }

theorem dramBankCorePrechargeWorld_eq_nominal
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (column : Fin columns) :
    dramBankCorePrechargeWorld profile world column =
      nominalDramPrechargeWorld 0 dramBankPrechargeHorizon := by
  simp [dramBankCorePrechargeWorld, nominalDramPrechargeWorld,
    hprofile.1 world.row column, nominalDramCellInstance]

noncomputable def dramBankCoreInitialEndpoint
    (bits : DramMatrixState rows columns)
    (prechargedBitline : Fin columns → ℝ) :
    DramArrayEndpoint rows columns where
  storage row column := dramBankCoreStoredVoltage (bits.bits row column)
  bitline column := prechargedBitline column

def DramProfileRowActivated
    (profile : DramBankCoreProfile rows columns)
    (selectedRow : Fin rows)
    (before after : DramArrayEndpoint rows columns) : Prop :=
  (∀ column,
    DramCellSettledRead (profile.cells selectedRow column)
      (before.cell selectedRow column)
      (after.cell selectedRow column)) ∧
  (∀ row, row ≠ selectedRow →
    ∀ column, after.storage row column = before.storage row column)

noncomputable def dramProfileActivatedEndpoint
    (profile : DramBankCoreProfile rows columns)
    (selectedRow : Fin rows)
    (before : DramArrayEndpoint rows columns) :
    DramArrayEndpoint rows columns where
  storage row column :=
    if row = selectedRow then
      dramCellSharedVoltage (profile.cells selectedRow column)
        (before.cell selectedRow column)
    else
      before.storage row column
  bitline column :=
    dramCellSharedVoltage (profile.cells selectedRow column)
      (before.cell selectedRow column)

theorem dramProfile_row_activation_realizable
    (profile : DramBankCoreProfile rows columns)
    (selectedRow : Fin rows)
    (before : DramArrayEndpoint rows columns)
    (hcapacitance :
      ∀ column,
        (profile.cells selectedRow column).storageCapacitance +
          (profile.cells selectedRow column).bitlineCapacitance ≠ 0) :
    ∃ after, DramProfileRowActivated profile selectedRow before after := by
  let after := dramProfileActivatedEndpoint profile selectedRow before
  refine ⟨after, ?_, ?_⟩
  · intro column
    have hcell :=
      dramCell_shared_endpoint_correct
        (profile.cells selectedRow column)
        (before.cell selectedRow column)
        (hcapacitance column)
    simpa [after, dramProfileActivatedEndpoint, DramArrayEndpoint.cell,
      dramCellSharedEndpoint] using hcell
  · intro row hrow column
    simp [after, dramProfileActivatedEndpoint, hrow]

theorem DramProfileRowActivated.selected_column
    {profile : DramBankCoreProfile rows columns}
    {selectedRow : Fin rows}
    {before after : DramArrayEndpoint rows columns}
    (hactivation :
      DramProfileRowActivated profile selectedRow before after)
    (column : Fin columns)
    (hstorageCap :
      0 < (profile.cells selectedRow column).storageCapacitance)
    (hbitlineCap :
      0 < (profile.cells selectedRow column).bitlineCapacitance) :
    after.storage selectedRow column =
        dramCellSharedVoltage (profile.cells selectedRow column)
          (before.cell selectedRow column) ∧
      after.bitline column =
        dramCellSharedVoltage (profile.cells selectedRow column)
          (before.cell selectedRow column) := by
  exact dramCell_shared_voltage hstorageCap hbitlineCap
    (hactivation.1 column).1 (hactivation.1 column).2

noncomputable def dramBankCoreUnselectedWorld
    (profile : DramBankCoreProfile rows columns)
    (world : DramBankCoreReadWorld rows columns)
    (row : Fin rows) (column : Fin columns) : Dram1T1CWorld :=
  deterministicWorld
    { threshold := (profile.cells row column).threshold
      beta := (profile.cells row column).beta
      storageCapacitance :=
        (profile.cells row column).storageCapacitance }
    { supply := 5
      mode := .hold
      initialVoltage :=
        dramBankCoreStoredVoltage (world.bits.bits row column)
      horizon := 1 }

noncomputable def dramBankCoreRestoreOneWorld
    (profile : DramBankCoreProfile rows columns)
    (world : DramBankCoreReadWorld rows columns)
    (observation : DramBankCoreReadObservation rows columns)
    (column : Fin columns) : DramWriteWorld :=
  deterministicWorld
    { threshold := (profile.cells world.row column).threshold
      beta := (profile.cells world.row column).beta
      storageCapacitance :=
        (profile.cells world.row column).storageCapacitance }
    { wordlineVoltage := 5
      bitlineVoltage := observation.senseOutput column
      initialStorage := observation.activated.storage world.row column
      horizon := dramBankCoreRestoreHorizon }

noncomputable def dramBankCoreRestoreZeroWorld
    (profile : DramBankCoreProfile rows columns)
    (world : DramBankCoreReadWorld rows columns)
    (observation : DramBankCoreReadObservation rows columns)
    (column : Fin columns) : Dram1T1CWorld :=
  deterministicWorld
    { threshold := (profile.cells world.row column).threshold
      beta := (profile.cells world.row column).beta
      storageCapacitance :=
        (profile.cells world.row column).storageCapacitance }
    { supply := 5
      mode := .writeZero
      initialVoltage := observation.activated.storage world.row column
      horizon := dramBankCoreRestoreHorizon }

noncomputable def nominalDramBankCoreRestoreZeroWorld
    (initialStorage : ℝ) : Dram1T1CWorld :=
  deterministicWorld
    { threshold := 1
      beta := 1 / 10000
      storageCapacitance := 3 / 100000000000000 }
    { supply := 5
      mode := .writeZero
      initialVoltage := initialStorage
      horizon := dramBankCoreRestoreHorizon }

theorem nominalDramBankCoreRestoreZeroWorld_admissible
    {initialStorage : ℝ}
    (hinitial0 : 0 ≤ initialStorage) (hinitial5 : initialStorage ≤ 5) :
    Dram1T1CAdmissible
      (nominalDramBankCoreRestoreZeroWorld initialStorage) := by
  norm_num [Dram1T1CAdmissible, nominalDramBankCoreRestoreZeroWorld,
    dramBankCoreRestoreHorizon, deterministicWorld, hinitial0, hinitial5]

noncomputable def dramBankCoreCanonicalRestoreZeroBoundary
    (initialStorage : ℝ) (hinitial0 : 0 ≤ initialStorage)
    (hinitial5 : initialStorage ≤ 5) :
    Dram1T1CBoundary :=
  Classical.choose
    (dram1T1C_realizable
      (nominalDramBankCoreRestoreZeroWorld initialStorage)
      (nominalDramBankCoreRestoreZeroWorld_admissible
        hinitial0 hinitial5))

theorem dramBankCoreCanonicalRestoreZeroBoundary_behaves :
    Dram1T1CBehavior
      (nominalDramBankCoreRestoreZeroWorld initialStorage)
      (dramBankCoreCanonicalRestoreZeroBoundary
        initialStorage hinitial0 hinitial5) () :=
  by
    have hinternal :=
      Classical.choose_spec
        (dram1T1C_realizable
          (nominalDramBankCoreRestoreZeroWorld initialStorage)
          (nominalDramBankCoreRestoreZeroWorld_admissible
            hinitial0 hinitial5))
    have hbehavior := Classical.choose_spec hinternal
    have hunit : Classical.choose hinternal = () :=
      Subsingleton.elim _ _
    rw [hunit] at hbehavior
    exact hbehavior

inductive DramBankCoreReadClause where
  | prechargeEvolution
  | prechargeEndpoint
  | rowActivation
  | senseDevice
  | readMuxConnection
  | restoreConnection
  | restoreEvolution
  | restoreStorageEndpoint
  | unselectedInitial
  | unselectedEvolution
  | unselectedEndpoint
deriving DecidableEq

noncomputable def DramBankCoreReadProgram
    (profile : DramBankCoreProfile rows columns) :
    EquationProgram DramBankCoreReadClause
      (DramBankCoreReadWorld rows columns)
      (DramBankCoreReadObservation rows columns) Unit where
  origin
    | .prechargeEvolution =>
        .evolution "per-column enabled MOS1 and bitline-capacitor precharge DAE"
    | .prechargeEndpoint =>
        .connectionLaw "precharge phase endpoint"
    | .rowActivation =>
        .deviceLaw "1T1C charge-sharing row"
    | .senseDevice =>
        .importedContract "legacy two-inverter sense endpoint contract"
    | .readMuxConnection =>
        .connectionLaw "selected read transmission gate"
    | .restoreConnection =>
        .connectionLaw "per-column restore transmission gate"
    | .restoreEvolution =>
        .evolution "selected-row 1T1C restore DAE"
    | .restoreStorageEndpoint =>
        .connectionLaw "selected storage restore phase endpoint"
    | .unselectedInitial =>
        .initialCondition "unselected 1T1C storage voltage"
    | .unselectedEvolution =>
        .evolution "unselected 1T1C hold DAE"
    | .unselectedEndpoint =>
        .connectionLaw "unselected storage phase endpoint"
  equation clause world observation _internal :=
    let before :=
      dramBankCoreInitialEndpoint world.bits observation.prechargedBitline
    match clause with
    | .prechargeEvolution =>
        ∀ column,
          DramPrechargeBehavior
            (dramBankCorePrechargeWorld profile world column)
            ⟨observation.prechargeTrace column⟩ ()
    | .prechargeEndpoint =>
        ∀ column,
          observation.prechargedBitline column =
            observation.prechargeTrace column dramBankPrechargeHorizon
    | .rowActivation =>
        DramProfileRowActivated profile world.row before
          observation.activated
    | .senseDevice =>
        ∀ column,
          DramSensePathEquations
            (observation.activated.bitline column)
            (observation.senseIntermediate column)
            (observation.senseOutput column)
    | .readMuxConnection =>
        DramTransmissionGateEquations
          (observation.senseOutput world.column) observation.dataOut
    | .restoreConnection =>
        ∀ column,
          DramTransmissionGateEquations
            (observation.senseOutput column)
            (observation.restored.bitline column)
    | .restoreEvolution =>
        ∀ column,
          if world.bits.bits world.row column then
            DramWriteBehavior
              (dramBankCoreRestoreOneWorld
                profile world observation column)
              ⟨observation.selectedRestoreTrace column⟩ ()
          else
            Dram1T1CBehavior
              (dramBankCoreRestoreZeroWorld
                profile world observation column)
              ⟨observation.selectedRestoreTrace column⟩ ()
    | .restoreStorageEndpoint =>
        ∀ column,
          observation.restored.storage world.row column =
            observation.selectedRestoreTrace column
              dramBankCoreRestoreHorizon
    | .unselectedInitial =>
        ∀ otherRow, otherRow ≠ world.row →
          ∀ column,
            observation.unselectedStorageTrace otherRow column 0 =
              before.storage otherRow column
    | .unselectedEvolution =>
        ∀ otherRow, otherRow ≠ world.row →
          ∀ column,
            dram1T1CDAE.ACBehavesOn
              (dramBankCoreUnselectedWorld
                profile world otherRow column)
              1 (observation.unselectedStorageTrace otherRow column)
    | .unselectedEndpoint =>
        ∀ otherRow, otherRow ≠ world.row →
          ∀ column,
            observation.restored.storage otherRow column =
              observation.unselectedStorageTrace otherRow column 1

noncomputable def DramBankCoreReadBehavior
    (profile : DramBankCoreProfile rows columns) :
    Behavior (DramBankCoreReadWorld rows columns)
      (DramBankCoreReadObservation rows columns) Unit :=
  (DramBankCoreReadProgram profile).behavior

theorem dramBankCoreReadEquationManifest :
    EquationManifest
      (DramBankCoreReadProgram
        (rows := rows) (columns := columns) profile)
      ["legacy two-inverter sense endpoint contract"] := by
  constructor
  ·
    intro contract hcontract
    simp at hcontract
    subst contract
    exact ⟨.senseDevice, rfl⟩
  ·
    intro contract hcontract
    rcases hcontract with ⟨clause, hclause⟩
    cases clause <;>
      simp [DramBankCoreReadProgram] at hclause ⊢
    all_goals subst contract <;> simp

noncomputable def DramBankCoreReadAllowed
    (profile : DramBankCoreProfile rows columns)
    (_world : DramBankCoreReadWorld rows columns) : Prop :=
  DramBankCoreNominalProfile profile

theorem dramBankCore_initial_shared_voltage
    {profile : DramBankCoreProfile rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (bits : DramMatrixState rows columns)
    (prechargedBitline : Fin columns → ℝ)
    (row : Fin rows) (column : Fin columns) :
    dramCellSharedVoltage (profile.cells row column)
        ((dramBankCoreInitialEndpoint bits prechargedBitline).cell
          row column) =
      if bits.bits row column then
        (4 + 10 * prechargedBitline column) / 11
      else
        10 * prechargedBitline column / 11 := by
  rw [hprofile.1 row column]
  cases hbit : bits.bits row column <;>
    norm_num [nominalDramCellInstance, dramCellSharedVoltage,
      dramCellEndpointCharge, DramArrayEndpoint.cell,
      dramBankCoreInitialEndpoint, dramBankCoreStoredVoltage,
      hbit] <;> ring

theorem DramBankCoreReadBehavior.precharged_voltage_bounds
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    {observation : DramBankCoreReadObservation rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (hbehavior :
      DramBankCoreReadBehavior profile world observation ()) :
    ∀ column,
      247 / 100 ≤ observation.prechargedBitline column ∧
        observation.prechargedBitline column ≤ 5 / 2 := by
  intro column
  have hevolution := hbehavior .prechargeEvolution column
  rw [dramBankCorePrechargeWorld_eq_nominal hprofile column] at hevolution
  have heq :=
    nominalDramPrecharge_behavior_eq_trace
      (initialVoltage := (0 : ℝ))
      (horizon := dramBankPrechargeHorizon)
      (boundary := ⟨observation.prechargeTrace column⟩)
      (by norm_num) (by norm_num)
      (by norm_num [dramBankPrechargeHorizon]) hevolution
      dramBankPrechargeHorizon
      (by norm_num [dramBankPrechargeHorizon])
  have hsettles :=
    nominalDramPrecharge_behavior_zero_ten_ns_settles hevolution
  have herror :=
    hsettles.2.2.2 dramBankPrechargeHorizon le_rfl le_rfl
  change
    |observation.prechargeTrace column dramBankPrechargeHorizon - 5 / 2| ≤
      3 / 100 at herror
  change
    observation.prechargeTrace column dramBankPrechargeHorizon =
      nominalDramPrechargeTrace 0 dramBankPrechargeHorizon at heq
  have hupper :=
    nominalDramPrechargeTrace_le_reference
      (initialVoltage := (0 : ℝ))
      (time := dramBankPrechargeHorizon)
      (by norm_num) (by norm_num [dramBankPrechargeHorizon])
  rw [hbehavior .prechargeEndpoint column, heq]
  rw [abs_le] at herror
  constructor <;> linarith

theorem dramBankCore_initial_shared_voltage_bounds
    {profile : DramBankCoreProfile rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (bits : DramMatrixState rows columns)
    (prechargedBitline : Fin columns → ℝ)
    (row : Fin rows) (column : Fin columns)
    (hprecharge :
      247 / 100 ≤ prechargedBitline column ∧
        prechargedBitline column ≤ 5 / 2) :
    if bits.bits row column then
      13 / 5 ≤
          dramCellSharedVoltage (profile.cells row column)
            ((dramBankCoreInitialEndpoint bits prechargedBitline).cell
              row column) ∧
        dramCellSharedVoltage (profile.cells row column)
            ((dramBankCoreInitialEndpoint bits prechargedBitline).cell
              row column) ≤ 29 / 11
    else
      247 / 110 ≤
          dramCellSharedVoltage (profile.cells row column)
            ((dramBankCoreInitialEndpoint bits prechargedBitline).cell
              row column) ∧
        dramCellSharedVoltage (profile.cells row column)
            ((dramBankCoreInitialEndpoint bits prechargedBitline).cell
              row column) ≤ 25 / 11 := by
  have heq :=
    dramBankCore_initial_shared_voltage hprofile bits
      prechargedBitline row column
  cases hbit : bits.bits row column
  · simp only [hbit, Bool.false_eq_true, if_false] at heq ⊢
    rw [heq]
    constructor <;> nlinarith [hprecharge.1, hprecharge.2]
  · simp only [hbit, if_true] at heq ⊢
    rw [heq]
    constructor <;> nlinarith [hprecharge.1, hprecharge.2]

theorem DramBankCoreReadBehavior.activated_cell_voltage
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    {observation : DramBankCoreReadObservation rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (hbehavior :
      DramBankCoreReadBehavior profile world observation ()) :
    ∀ column,
      observation.activated.storage world.row column =
          observation.activated.bitline column ∧
        if world.bits.bits world.row column then
          13 / 5 ≤ observation.activated.bitline column ∧
            observation.activated.bitline column ≤ 29 / 11
        else
          247 / 110 ≤ observation.activated.bitline column ∧
            observation.activated.bitline column ≤ 25 / 11 := by
  intro column
  have hprecharge := hbehavior.precharged_voltage_bounds hprofile column
  have hactivation := hbehavior .rowActivation
  have hselected :=
    hactivation.selected_column column (by
      rw [hprofile.1 world.row column]
      norm_num [nominalDramCellInstance]) (by
      rw [hprofile.1 world.row column]
      norm_num [nominalDramCellInstance])
  have hbounds :=
    dramBankCore_initial_shared_voltage_bounds hprofile world.bits
      observation.prechargedBitline world.row column hprecharge
  rw [hselected.1, hselected.2]
  exact ⟨rfl, hbounds⟩

theorem DramBankCoreReadBehavior.activated_voltage
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    {observation : DramBankCoreReadObservation rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (hbehavior :
      DramBankCoreReadBehavior profile world observation ()) :
    ∀ column,
      if world.bits.bits world.row column then
        13 / 5 ≤ observation.activated.bitline column ∧
          observation.activated.bitline column ≤ 29 / 11
      else
        247 / 110 ≤ observation.activated.bitline column ∧
          observation.activated.bitline column ≤ 25 / 11 := by
  intro column
  exact (hbehavior.activated_cell_voltage hprofile column).2

/-- Physical precharge and charge sharing deliver a uniform differential
relative to an otherwise precharged reference bitline. For a stored one the
selected bitline is higher; for a stored zero it is lower. The `3/22 V`
margin is the tighter of the two nominal charge-sharing bounds. -/
theorem DramBankCoreReadBehavior.activated_reference_margin
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    {observation : DramBankCoreReadObservation rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (hbehavior :
      DramBankCoreReadBehavior profile world observation ()) :
    ∀ column,
      if world.bits.bits world.row column then
        observation.prechargedBitline column + 3 / 22 ≤
          observation.activated.bitline column
      else
        observation.activated.bitline column + 3 / 22 ≤
          observation.prechargedBitline column := by
  intro column
  have hprecharge :=
    hbehavior.precharged_voltage_bounds hprofile column
  have hactivation := hbehavior .rowActivation
  have hselected :=
    hactivation.selected_column column (by
      rw [hprofile.1 world.row column]
      norm_num [nominalDramCellInstance]) (by
      rw [hprofile.1 world.row column]
      norm_num [nominalDramCellInstance])
  have hshared :=
    dramBankCore_initial_shared_voltage hprofile world.bits
      observation.prechargedBitline world.row column
  cases hbit : world.bits.bits world.row column
  · simp only [hbit, Bool.false_eq_true, if_false] at hshared ⊢
    rw [hselected.2, hshared]
    nlinarith [hprecharge.1]
  · simp only [hbit, if_true] at hshared ⊢
    rw [hselected.2, hshared]
    nlinarith [hprecharge.2]

theorem DramBankCoreReadBehavior.sense_correct
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    {observation : DramBankCoreReadObservation rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (hbehavior :
      DramBankCoreReadBehavior profile world observation ()) :
    ∀ column,
      observation.senseOutput column =
        logicVoltage (world.bits.bits world.row column) := by
  intro column
  have hvoltage := hbehavior.activated_voltage hprofile column
  have hsenseColumn := hbehavior .senseDevice column
  cases hbit : world.bits.bits world.row column
  · rw [hbit] at hvoltage
    simp only [Bool.false_eq_true, ↓reduceIte] at hvoltage
    exact dramSensePath_readZero_of_input_le
      (by linarith [hvoltage.1]) (by linarith [hvoltage.2]) hsenseColumn
  · rw [hbit] at hvoltage
    simp only [↓reduceIte] at hvoltage
    exact dramSensePath_readOne_of_input_ge
      hvoltage.1 (by linarith [hvoltage.2]) hsenseColumn

/-- The selected storage endpoint is the value reached by its physical restore
trajectory at the declared finite horizon. The bitline endpoint is connected
to the sense output. No target storage voltage occurs in the behavior. -/
theorem DramBankCoreReadBehavior.restored_selected_cell
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    {observation : DramBankCoreReadObservation rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (hbehavior :
      DramBankCoreReadBehavior profile world observation ()) :
    ∀ column,
      observation.restored.storage world.row column =
          observation.selectedRestoreTrace column
            dramBankCoreRestoreHorizon ∧
        observation.restored.bitline column =
          logicVoltage (world.bits.bits world.row column) := by
  intro column
  have hstorage := hbehavior .restoreStorageEndpoint column
  have hbitline :=
    (dramTransmissionGate_correct
      (hbehavior .restoreConnection column)).trans
      (hbehavior.sense_correct hprofile column)
  exact ⟨hstorage, hbitline⟩

theorem dramBankCore_restore_one_world_eq_nominal
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    {observation : DramBankCoreReadObservation rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (hbehavior :
      DramBankCoreReadBehavior profile world observation ())
    (column : Fin columns)
    (hbit : world.bits.bits world.row column = true) :
    dramBankCoreRestoreOneWorld profile world observation column =
      nominalDramWriteOneWorld
        (observation.activated.storage world.row column)
        dramBankCoreRestoreHorizon := by
  have hsense := hbehavior.sense_correct hprofile column
  rw [hbit] at hsense
  simp only [logicVoltage] at hsense
  simp [dramBankCoreRestoreOneWorld, nominalDramWriteOneWorld,
    hprofile.1 world.row column, nominalDramCellInstance,
    hsense]

theorem dramBankCore_restore_zero_world_eq_nominal
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    {observation : DramBankCoreReadObservation rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (hbehavior :
      DramBankCoreReadBehavior profile world observation ())
    (column : Fin columns)
    (hbit : world.bits.bits world.row column = false) :
    dramBankCoreRestoreZeroWorld profile world observation column =
      nominalDramBankCoreRestoreZeroWorld
        (observation.activated.storage world.row column) := by
  simp [dramBankCoreRestoreZeroWorld,
    nominalDramBankCoreRestoreZeroWorld,
    hprofile.1 world.row column, nominalDramCellInstance]

/-- Every selected restore trajectory stays in the physical unboosted-NMOS
range. The upper endpoint is the 4 V threshold-loss boundary, not an asserted
postcondition. -/
theorem DramBankCoreReadBehavior.restored_selected_storage_bounds
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    {observation : DramBankCoreReadObservation rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (hbehavior :
      DramBankCoreReadBehavior profile world observation ()) :
    ∀ column,
      0 ≤ observation.restored.storage world.row column ∧
        observation.restored.storage world.row column ≤ 4 := by
  intro column
  have hendpoint :=
    (hbehavior.restored_selected_cell hprofile column).1
  have hevolution := hbehavior .restoreEvolution column
  cases hbit : world.bits.bits world.row column
  · rw [if_neg (by simpa using hbit)] at hevolution
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
    rw [dramBankCore_restore_zero_world_eq_nominal
      hprofile hbehavior column hbit] at hevolution
    have hloaded :
        LoadedInverterBehavior
          (nominalDramBankCoreRestoreZeroWorld
            (observation.activated.storage world.row column)).asLoadedInverter
          ⟨observation.selectedRestoreTrace column⟩ () := by
      simpa [Dram1T1CBehavior, Dram1T1CProgram,
        nominalDramBankCoreRestoreZeroWorld, deterministicWorld] using
          hevolution .evolution
    have hadmissible :=
      (nominalDramBankCoreRestoreZeroWorld_admissible
        hinitial0 hinitial5).asLoadedInverter
    have htime :
        dramBankCoreRestoreHorizon ∈
          Icc (0 : ℝ)
            (nominalDramBankCoreRestoreZeroWorld
              (observation.activated.storage world.row column)).environment.horizon := by
      norm_num [nominalDramBankCoreRestoreZeroWorld,
        dramBankCoreRestoreHorizon, deterministicWorld]
    have hdomain :=
      loadedInverter_no_overshoot hadmissible hloaded.2
        dramBankCoreRestoreHorizon htime
    have hantitone :=
      loadedInverter_antitone_discharging hadmissible rfl hloaded.2
    have hstart :
        observation.selectedRestoreTrace column
            dramBankCoreRestoreHorizon ≤
          observation.selectedRestoreTrace column 0 :=
      hantitone
        (show (0 : ℝ) ∈
            Icc 0
              (nominalDramBankCoreRestoreZeroWorld
                (observation.activated.storage world.row column)).environment.horizon by
          norm_num [nominalDramBankCoreRestoreZeroWorld,
            dramBankCoreRestoreHorizon, deterministicWorld])
        htime htime.1
    have hinitial :
        observation.selectedRestoreTrace column 0 =
          observation.activated.storage world.row column := by
      simpa [nominalDramBankCoreRestoreZeroWorld,
        Dram1T1CWorld.asLoadedInverter, deterministicWorld] using
          hloaded.2.1
    rw [hendpoint]
    exact
      ⟨hdomain.1,
        by rw [hinitial] at hstart
           rw [hactivated.1] at hstart
           linarith [hactivated.2.2]⟩
  · rw [if_pos hbit] at hevolution
    have hactivated :=
      hbehavior.activated_cell_voltage hprofile column
    rw [hbit] at hactivated
    simp only [if_true] at hactivated
    have hinitial0 :
        0 ≤ observation.activated.storage world.row column := by
      rw [hactivated.1]
      linarith [hactivated.2.1]
    have hinitial4 :
        observation.activated.storage world.row column ≤ 4 := by
      rw [hactivated.1]
      linarith [hactivated.2.2]
    rw [dramBankCore_restore_one_world_eq_nominal
      hprofile hbehavior column hbit] at hevolution
    have heq :=
      nominalDramWriteOne_behavior_eq_trace
        (initialStorage :=
          observation.activated.storage world.row column)
        (horizon := dramBankCoreRestoreHorizon)
        (boundary := ⟨observation.selectedRestoreTrace column⟩)
        hinitial4
        (by norm_num [dramBankCoreRestoreHorizon])
        hevolution dramBankCoreRestoreHorizon
        (by norm_num [dramBankCoreRestoreHorizon])
    have hlower :=
      nominalDramWriteOneTrace_mono_from_initial
        (initialStorage :=
          observation.activated.storage world.row column)
        (time := dramBankCoreRestoreHorizon)
        hinitial4 (by norm_num [dramBankCoreRestoreHorizon])
    have hupper :=
      nominalDramWriteOneTrace_le_target
        (initialStorage :=
          observation.activated.storage world.row column)
        (time := dramBankCoreRestoreHorizon)
        hinitial4 (by norm_num [dramBankCoreRestoreHorizon])
    have heq' :
        observation.selectedRestoreTrace column
            dramBankCoreRestoreHorizon =
          nominalDramWriteOneTrace
            (observation.activated.storage world.row column)
            dramBankCoreRestoreHorizon := by
      simpa using heq
    rw [hendpoint, heq']
    exact ⟨by linarith [hlower, hinitial0], hupper⟩

theorem DramBankCoreReadBehavior.unselected_preserved
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    {observation : DramBankCoreReadObservation rows columns}
    (hbehavior :
      DramBankCoreReadBehavior profile world observation ()) :
    ∀ otherRow, otherRow ≠ world.row →
      ∀ column,
        observation.restored.storage otherRow column =
          (dramBankCoreInitialEndpoint world.bits
            observation.prechargedBitline).storage otherRow column := by
  intro otherRow hother column
  have hinitial :=
    hbehavior .unselectedInitial otherRow hother column
  have hevolution :=
    hbehavior .unselectedEvolution otherRow hother column
  have hendpoint :=
    hbehavior .unselectedEndpoint otherRow hother column
  have hconstant :=
    dram1T1CDAE.constant_on_of_residual_forces_zero hevolution
      (fun _time _storage derivative hresidual => by
        simpa [dram1T1CDAE, dram1T1CField,
          dramBankCoreUnselectedWorld, deterministicWorld] using hresidual)
  calc
    observation.restored.storage otherRow column =
        observation.unselectedStorageTrace otherRow column 1 :=
      hendpoint
    _ = observation.unselectedStorageTrace otherRow column 0 :=
      hconstant 1 (by norm_num)
    _ = (dramBankCoreInitialEndpoint world.bits
          observation.prechargedBitline).storage otherRow column :=
      hinitial

noncomputable def dramBankCoreCanonicalPrechargeTrace
    (_column : Fin columns) : DenseTrace ℝ :=
  nominalDramPrechargeTrace 0

noncomputable def dramBankCoreCanonicalPrechargedBitline
    (column : Fin columns) : ℝ :=
  dramBankCoreCanonicalPrechargeTrace column dramBankPrechargeHorizon

theorem dramBankCoreCanonicalPrechargedBitline_bounds
    (column : Fin columns) :
    247 / 100 ≤
        dramBankCoreCanonicalPrechargedBitline column ∧
      dramBankCoreCanonicalPrechargedBitline column ≤ 5 / 2 := by
  have hsettles := nominalDramPrecharge_zero_ten_ns_settles
  have herror :=
    hsettles.2.2.2 dramBankPrechargeHorizon le_rfl le_rfl
  have hupper :=
    nominalDramPrechargeTrace_le_reference
      (initialVoltage := (0 : ℝ))
      (time := dramBankPrechargeHorizon)
      (by norm_num) (by norm_num [dramBankPrechargeHorizon])
  change
    |dramBankCoreCanonicalPrechargedBitline column - 5 / 2| ≤
      3 / 100 at herror
  rw [abs_le] at herror
  exact ⟨by linarith, hupper⟩

noncomputable def dramBankCoreCanonicalActivated
    (profile : DramBankCoreProfile rows columns)
    (world : DramBankCoreReadWorld rows columns) :
  DramArrayEndpoint rows columns :=
  dramProfileActivatedEndpoint profile world.row
    (dramBankCoreInitialEndpoint world.bits
      dramBankCoreCanonicalPrechargedBitline)

theorem dramBankCoreCanonicalActivated_cell
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (column : Fin columns) :
    (dramBankCoreCanonicalActivated profile world).storage
          world.row column =
        (dramBankCoreCanonicalActivated profile world).bitline column ∧
      if world.bits.bits world.row column then
        13 / 5 ≤
            (dramBankCoreCanonicalActivated profile world).bitline column ∧
          (dramBankCoreCanonicalActivated profile world).bitline column ≤
            29 / 11
      else
        247 / 110 ≤
            (dramBankCoreCanonicalActivated profile world).bitline column ∧
          (dramBankCoreCanonicalActivated profile world).bitline column ≤
            25 / 11 := by
  have hbounds :=
    dramBankCore_initial_shared_voltage_bounds hprofile world.bits
      dramBankCoreCanonicalPrechargedBitline world.row column
      (dramBankCoreCanonicalPrechargedBitline_bounds column)
  constructor
  · simp [dramBankCoreCanonicalActivated,
      dramProfileActivatedEndpoint]
  · simpa [dramBankCoreCanonicalActivated,
      dramProfileActivatedEndpoint] using hbounds

theorem dramBankCoreCanonicalActivated_input_bounds
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (column : Fin columns) :
    0 ≤ (dramBankCoreCanonicalActivated profile world).bitline column ∧
      (dramBankCoreCanonicalActivated profile world).bitline column ≤ 5 := by
  have hbounds :=
    (dramBankCoreCanonicalActivated_cell
      (world := world) hprofile column).2
  cases hbit : world.bits.bits world.row column
  · simp only [hbit, Bool.false_eq_true, if_false] at hbounds
    constructor <;> linarith [hbounds.1, hbounds.2]
  · simp only [hbit, if_true] at hbounds
    constructor <;> linarith [hbounds.1, hbounds.2]

noncomputable def dramBankCoreCanonicalSensePair
    (profile : DramBankCoreProfile rows columns)
    (world : DramBankCoreReadWorld rows columns)
    (hprofile : DramBankCoreNominalProfile profile)
    (column : Fin columns) : ℝ × ℝ :=
  let hexists :=
    dramSensePath_realizable
      (dramBankCoreCanonicalActivated_input_bounds
        (world := world) hprofile column).1
      (dramBankCoreCanonicalActivated_input_bounds
        (world := world) hprofile column).2
  let intermediate := Classical.choose hexists
  let houtput := Classical.choose_spec hexists
  (intermediate, Classical.choose houtput)

theorem dramBankCoreCanonicalSensePair_spec
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (column : Fin columns) :
    DramSensePathEquations
      ((dramBankCoreCanonicalActivated profile world).bitline column)
      (dramBankCoreCanonicalSensePair profile world hprofile column).1
    (dramBankCoreCanonicalSensePair profile world hprofile column).2 := by
  let hexists :=
    dramSensePath_realizable
      (dramBankCoreCanonicalActivated_input_bounds
        (world := world) hprofile column).1
      (dramBankCoreCanonicalActivated_input_bounds
        (world := world) hprofile column).2
  exact Classical.choose_spec (Classical.choose_spec hexists)

theorem dramBankCoreCanonicalSensePair_correct
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (column : Fin columns) :
    (dramBankCoreCanonicalSensePair profile world hprofile column).2 =
      logicVoltage (world.bits.bits world.row column) := by
  have hactivated :=
    (dramBankCoreCanonicalActivated_cell
      (world := world) hprofile column).2
  have hsense :=
    dramBankCoreCanonicalSensePair_spec
      (world := world) hprofile column
  cases hbit : world.bits.bits world.row column
  · simp only [hbit, Bool.false_eq_true, if_false] at hactivated
    exact dramSensePath_readZero_of_input_le
      (by linarith [hactivated.1])
      (by linarith [hactivated.2]) hsense
  · simp only [hbit, if_true] at hactivated
    exact dramSensePath_readOne_of_input_ge
      hactivated.1 (by linarith [hactivated.2]) hsense

theorem dramBankCoreCanonicalActivated_storage_bounds
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreReadWorld rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (column : Fin columns) :
    0 ≤ (dramBankCoreCanonicalActivated profile world).storage
          world.row column ∧
      (dramBankCoreCanonicalActivated profile world).storage
          world.row column ≤ 4 := by
  have hcell :=
    dramBankCoreCanonicalActivated_cell
      (world := world) hprofile column
  rw [hcell.1]
  cases hbit : world.bits.bits world.row column
  · simp only [hbit, Bool.false_eq_true, if_false] at hcell
    constructor <;> linarith [hcell.2.1, hcell.2.2]
  · simp only [hbit, if_true] at hcell
    constructor <;> linarith [hcell.2.1, hcell.2.2]

noncomputable def dramBankCoreCanonicalRestoreTrace
    (profile : DramBankCoreProfile rows columns)
    (world : DramBankCoreReadWorld rows columns)
    (hprofile : DramBankCoreNominalProfile profile)
    (column : Fin columns) : DenseTrace ℝ :=
  if world.bits.bits world.row column then
    nominalDramWriteOneTrace
      ((dramBankCoreCanonicalActivated profile world).storage
        world.row column)
  else
    (dramBankCoreCanonicalRestoreZeroBoundary
      ((dramBankCoreCanonicalActivated profile world).storage
        world.row column)
      (dramBankCoreCanonicalActivated_storage_bounds
        (world := world) hprofile column).1
      (by
        linarith [
          (dramBankCoreCanonicalActivated_storage_bounds
            (world := world) hprofile column).2])).storageVoltage

noncomputable def dramBankCoreCanonicalRestored
    (profile : DramBankCoreProfile rows columns)
    (world : DramBankCoreReadWorld rows columns)
    (hprofile : DramBankCoreNominalProfile profile) :
    DramArrayEndpoint rows columns where
  storage row column :=
    if row = world.row then
      dramBankCoreCanonicalRestoreTrace profile world hprofile column
        dramBankCoreRestoreHorizon
    else
      dramBankCoreStoredVoltage (world.bits.bits row column)
  bitline column :=
    (dramBankCoreCanonicalSensePair profile world hprofile column).2

noncomputable def dramBankCoreCanonicalReadObservation
    (profile : DramBankCoreProfile rows columns)
    (world : DramBankCoreReadWorld rows columns)
    (hprofile : DramBankCoreNominalProfile profile) :
    DramBankCoreReadObservation rows columns where
  prechargeTrace := dramBankCoreCanonicalPrechargeTrace
  prechargedBitline := dramBankCoreCanonicalPrechargedBitline
  activated := dramBankCoreCanonicalActivated profile world
  senseIntermediate column :=
    (dramBankCoreCanonicalSensePair profile world hprofile column).1
  senseOutput column :=
    (dramBankCoreCanonicalSensePair profile world hprofile column).2
  dataOut :=
    (dramBankCoreCanonicalSensePair profile world hprofile world.column).2
  selectedRestoreTrace :=
    dramBankCoreCanonicalRestoreTrace profile world hprofile
  unselectedStorageTrace row column _time :=
    dramBankCoreStoredVoltage (world.bits.bits row column)
  restored := dramBankCoreCanonicalRestored profile world hprofile

theorem dramBankCore_read_realizable
    (profile : DramBankCoreProfile rows columns) :
    RealizableUnder (DramBankCoreReadBehavior profile)
      (DramBankCoreReadAllowed profile) := by
  intro world hprofile
  let observation :=
    dramBankCoreCanonicalReadObservation profile world hprofile
  refine ⟨observation, (), ?_⟩
  change ∀ clause,
    (DramBankCoreReadProgram profile).equation clause world observation ()
  intro clause
  cases clause
  case prechargeEvolution =>
    intro column
    rw [dramBankCorePrechargeWorld_eq_nominal hprofile column]
    intro prechargeClause
    cases prechargeClause
    · exact nominalDramPrechargeTrace_initial 0
    · exact
        ⟨nominalDramPrechargeTrace_physical
            (by norm_num)
            (by norm_num [dramBankPrechargeHorizon]),
          nominalDramPrechargeTrace_smooth
            (by norm_num)
            (by norm_num [dramBankPrechargeHorizon])⟩
  case prechargeEndpoint =>
    intro column
    rfl
  case rowActivation =>
    constructor
    · intro column
      have hcell := dramCell_shared_endpoint_correct
        (profile.cells world.row column)
        ((dramBankCoreInitialEndpoint world.bits
          dramBankCoreCanonicalPrechargedBitline).cell
          world.row column)
        (by
          rw [hprofile.1 world.row column]
          norm_num [nominalDramCellInstance])
      simpa [observation, dramBankCoreCanonicalReadObservation,
        dramBankCoreCanonicalActivated,
        dramProfileActivatedEndpoint, DramArrayEndpoint.cell,
        dramCellSharedEndpoint] using hcell
    · intro otherRow hother column
      simp [observation, dramBankCoreCanonicalReadObservation,
        dramBankCoreCanonicalActivated,
        dramProfileActivatedEndpoint, hother]
  case senseDevice =>
    intro column
    simpa [observation, dramBankCoreCanonicalReadObservation] using
      dramBankCoreCanonicalSensePair_spec
        (world := world) hprofile column
  case readMuxConnection =>
    have hbounds :=
      (dramBankCoreCanonicalSensePair_spec
        (world := world) hprofile world.column).2.1
    apply dramTransmissionGate_realizable
    · simpa [observation, dramBankCoreCanonicalReadObservation] using
        hbounds.1
    · simpa [observation, dramBankCoreCanonicalReadObservation] using
        hbounds.2
  case restoreConnection =>
    intro column
    have hbounds :=
      (dramBankCoreCanonicalSensePair_spec
        (world := world) hprofile column).2.1
    apply dramTransmissionGate_realizable
    · simpa [observation, dramBankCoreCanonicalReadObservation] using
        hbounds.1
    · simpa [observation, dramBankCoreCanonicalReadObservation] using
        hbounds.2
  case restoreEvolution =>
    intro column
    have hstorage :=
      dramBankCoreCanonicalActivated_storage_bounds
        (world := world) hprofile column
    cases hbit : world.bits.bits world.row column
    ·
      rw [if_neg (by simpa using hbit)]
      change Dram1T1CBehavior
        (dramBankCoreRestoreZeroWorld profile world
          observation column)
        ⟨dramBankCoreCanonicalRestoreTrace
          profile world hprofile column⟩ ()
      rw [show
        dramBankCoreRestoreZeroWorld profile world
            observation column =
          nominalDramBankCoreRestoreZeroWorld
            ((dramBankCoreCanonicalActivated profile world).storage
              world.row column) by
        simp [dramBankCoreRestoreZeroWorld,
          nominalDramBankCoreRestoreZeroWorld,
          observation,
          dramBankCoreCanonicalReadObservation,
          hprofile.1 world.row column, nominalDramCellInstance]
      ]
      simpa [dramBankCoreCanonicalRestoreTrace, hbit] using
        (dramBankCoreCanonicalRestoreZeroBoundary_behaves
          (initialStorage :=
            (dramBankCoreCanonicalActivated profile world).storage
              world.row column)
          (hinitial0 := hstorage.1)
          (hinitial5 := by linarith [hstorage.2]))
    ·
      simp only [if_true]
      change DramWriteBehavior
        (dramBankCoreRestoreOneWorld profile world
          observation column)
        ⟨dramBankCoreCanonicalRestoreTrace
          profile world hprofile column⟩ ()
      rw [show
        dramBankCoreRestoreOneWorld profile world
            observation column =
          nominalDramWriteOneWorld
            ((dramBankCoreCanonicalActivated profile world).storage
              world.row column)
            dramBankCoreRestoreHorizon by
        simp [dramBankCoreRestoreOneWorld,
          observation,
          dramBankCoreCanonicalReadObservation,
          hprofile.1 world.row column, nominalDramCellInstance,
          dramBankCoreCanonicalSensePair_correct
            (world := world) hprofile column,
          hbit, logicVoltage, nominalDramWriteOneWorld]
      ]
      simp only [dramBankCoreCanonicalRestoreTrace, hbit, if_true]
      intro writeClause
      cases writeClause
      · exact nominalDramWriteOneTrace_initial _
      · exact nominalDramWriteOneTrace_physical
          hstorage.2
          (by norm_num [dramBankCoreRestoreHorizon,
            nominalDramWriteOneWorld, deterministicWorld])
  case restoreStorageEndpoint =>
    intro column
    simp [observation, dramBankCoreCanonicalReadObservation,
      dramBankCoreCanonicalRestored]
  case unselectedInitial =>
    intro otherRow hother column
    rfl
  case unselectedEvolution =>
    intro otherRow hother column
    exact dram1T1C_hold_dae_realizable rfl
      (by simp [dramBankCoreUnselectedWorld, deterministicWorld])
  case unselectedEndpoint =>
    intro otherRow hother column
    simp [observation, dramBankCoreCanonicalReadObservation,
      dramBankCoreCanonicalRestored, hother]

structure DramBankCoreWriteWorld (rows columns : Nat) where
  bits : DramMatrixState rows columns
  row : Fin rows
  column : Fin columns
  value : Bool

def DramBankCoreWriteWorld.readWorld
    (world : DramBankCoreWriteWorld rows columns) :
    DramBankCoreReadWorld rows columns :=
  { bits := world.bits, row := world.row, column := world.column }

structure DramBankCoreWriteObservation (rows columns : Nat) where
  readPhase : DramBankCoreReadObservation rows columns
  writeBus : ℝ
  selectedStorageTrace : DenseTrace ℝ
  unselectedStorageTrace : Fin rows → Fin columns → DenseTrace ℝ
  unselectedColumnTrace : Fin columns → DenseTrace ℝ
  after : DramArrayEndpoint rows columns

noncomputable def dramBankCoreWriteHorizon : ℝ :=
  1 / 1000000000

noncomputable def dramBankCoreWriteInstance
    (profile : DramBankCoreProfile rows columns)
    (world : DramBankCoreWriteWorld rows columns) : DramWriteInstance :=
  { threshold := (profile.cells world.row world.column).threshold
    beta := (profile.cells world.row world.column).beta
    storageCapacitance :=
      (profile.cells world.row world.column).storageCapacitance }

noncomputable def dramBankCoreSelectedWriteOneWorld
    (profile : DramBankCoreProfile rows columns)
    (world : DramBankCoreWriteWorld rows columns)
    (readPhase : DramBankCoreReadObservation rows columns) : DramWriteWorld :=
  deterministicWorld
    (dramBankCoreWriteInstance profile world)
    { wordlineVoltage := 5
      bitlineVoltage := 5
      initialStorage := readPhase.restored.storage world.row world.column
      horizon := dramBankCoreWriteHorizon }

noncomputable def dramBankCoreSelectedWriteZeroWorld
    (profile : DramBankCoreProfile rows columns)
    (world : DramBankCoreWriteWorld rows columns)
    (readPhase : DramBankCoreReadObservation rows columns) : Dram1T1CWorld :=
  deterministicWorld
    { threshold := (profile.cells world.row world.column).threshold
      beta := (profile.cells world.row world.column).beta
      storageCapacitance :=
        (profile.cells world.row world.column).storageCapacitance }
    { supply := 5
      mode := .writeZero
      initialVoltage := readPhase.restored.storage world.row world.column
      horizon := dramBankCoreWriteHorizon }

noncomputable def nominalDramBankCoreWriteZeroWorld
    (initialStorage : ℝ) : Dram1T1CWorld :=
  deterministicWorld
    { threshold := 1
      beta := 1 / 10000
      storageCapacitance := 3 / 100000000000000 }
    { supply := 5
      mode := .writeZero
      initialVoltage := initialStorage
      horizon := dramBankCoreWriteHorizon }

theorem dramBankCore_selected_write_one_world_eq_nominal
    {profile : DramBankCoreProfile rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (world : DramBankCoreWriteWorld rows columns)
    (readPhase : DramBankCoreReadObservation rows columns) :
    dramBankCoreSelectedWriteOneWorld profile world readPhase =
      nominalDramWriteOneWorld
        (readPhase.restored.storage world.row world.column)
        dramBankCoreWriteHorizon := by
  simp [dramBankCoreSelectedWriteOneWorld, dramBankCoreWriteInstance,
    hprofile.1 world.row world.column, nominalDramCellInstance,
    nominalDramWriteOneWorld]

theorem dramBankCore_selected_write_zero_world_eq_nominal
    {profile : DramBankCoreProfile rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (world : DramBankCoreWriteWorld rows columns)
    (readPhase : DramBankCoreReadObservation rows columns) :
    dramBankCoreSelectedWriteZeroWorld profile world readPhase =
      nominalDramBankCoreWriteZeroWorld
        (readPhase.restored.storage world.row world.column) := by
  simp [dramBankCoreSelectedWriteZeroWorld,
    hprofile.1 world.row world.column, nominalDramCellInstance,
    nominalDramBankCoreWriteZeroWorld]

noncomputable def dramBankCoreWriteUnselectedWorld
    (profile : DramBankCoreProfile rows columns)
    (readPhase : DramBankCoreReadObservation rows columns)
    (row : Fin rows) (column : Fin columns) : Dram1T1CWorld :=
  deterministicWorld
    { threshold := (profile.cells row column).threshold
      beta := (profile.cells row column).beta
      storageCapacitance :=
        (profile.cells row column).storageCapacitance }
    { supply := 5
      mode := .hold
      initialVoltage := readPhase.restored.storage row column
      horizon := 1 }

noncomputable def dramBankCoreWriteUnselectedColumnOneWorld
    (profile : DramBankCoreProfile rows columns)
    (world : DramBankCoreWriteWorld rows columns)
    (readPhase : DramBankCoreReadObservation rows columns)
    (column : Fin columns) : DramWriteWorld :=
  deterministicWorld
    { threshold := (profile.cells world.row column).threshold
      beta := (profile.cells world.row column).beta
      storageCapacitance :=
        (profile.cells world.row column).storageCapacitance }
    { wordlineVoltage := 5
      bitlineVoltage := readPhase.senseOutput column
      initialStorage := readPhase.restored.storage world.row column
      horizon := dramBankCoreWriteHorizon }

noncomputable def dramBankCoreWriteUnselectedColumnZeroWorld
    (profile : DramBankCoreProfile rows columns)
    (world : DramBankCoreWriteWorld rows columns)
    (readPhase : DramBankCoreReadObservation rows columns)
    (column : Fin columns) : Dram1T1CWorld :=
  deterministicWorld
    { threshold := (profile.cells world.row column).threshold
      beta := (profile.cells world.row column).beta
      storageCapacitance :=
        (profile.cells world.row column).storageCapacitance }
    { supply := 5
      mode := .writeZero
      initialVoltage := readPhase.restored.storage world.row column
      horizon := dramBankCoreWriteHorizon }

theorem dramBankCore_unselected_column_one_world_eq_nominal
    {profile : DramBankCoreProfile rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (world : DramBankCoreWriteWorld rows columns)
    (readPhase : DramBankCoreReadObservation rows columns)
    (hread :
      DramBankCoreReadBehavior profile world.readWorld readPhase ())
    (column : Fin columns)
    (hbit : world.bits.bits world.row column = true) :
    dramBankCoreWriteUnselectedColumnOneWorld
        profile world readPhase column =
      nominalDramWriteOneWorld
        (readPhase.restored.storage world.row column)
        dramBankCoreWriteHorizon := by
  have hsense := hread.sense_correct hprofile column
  simp only [DramBankCoreWriteWorld.readWorld] at hsense
  rw [hbit] at hsense
  simp only [logicVoltage] at hsense
  simp [dramBankCoreWriteUnselectedColumnOneWorld,
    hprofile.1 world.row column, nominalDramCellInstance,
    hsense, nominalDramWriteOneWorld]

theorem dramBankCore_unselected_column_zero_world_eq_nominal
    {profile : DramBankCoreProfile rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (world : DramBankCoreWriteWorld rows columns)
    (readPhase : DramBankCoreReadObservation rows columns)
    (column : Fin columns) :
    dramBankCoreWriteUnselectedColumnZeroWorld
        profile world readPhase column =
      nominalDramBankCoreWriteZeroWorld
        (readPhase.restored.storage world.row column) := by
  simp [dramBankCoreWriteUnselectedColumnZeroWorld,
    hprofile.1 world.row column, nominalDramCellInstance,
    nominalDramBankCoreWriteZeroWorld]

inductive DramBankCoreWriteClause where
  | readEndpoint
  | writeBusConnection
  | selectedBitlineConnection
  | selectedStorageEvolution
  | selectedStorageEndpoint
  | unselectedStorageInitial
  | unselectedStorageEvolution
  | unselectedStorageEndpoint
  | unselectedColumnEvolution
  | unselectedColumnStorageEndpoint
  | unselectedColumnBitlineEndpoint
deriving DecidableEq

noncomputable def DramBankCoreWriteProgram
    (profile : DramBankCoreProfile rows columns) :
    EquationProgram DramBankCoreWriteClause
      (DramBankCoreWriteWorld rows columns)
      (DramBankCoreWriteObservation rows columns) Unit where
  origin
    | .readEndpoint =>
        .importedContract "read endpoint phase"
    | .writeBusConnection =>
        .connectionLaw "write input transmission gate"
    | .selectedBitlineConnection =>
        .connectionLaw "selected-column write transmission gate"
    | .selectedStorageEvolution =>
        .evolution "selected 1T1C write DAE"
    | .selectedStorageEndpoint =>
        .connectionLaw "selected storage write phase endpoint"
    | .unselectedStorageInitial =>
        .initialCondition "write-unselected 1T1C storage voltage"
    | .unselectedStorageEvolution =>
        .evolution "write-unselected 1T1C hold DAE"
    | .unselectedStorageEndpoint =>
        .connectionLaw "write-unselected storage phase endpoint"
    | .unselectedColumnEvolution =>
        .evolution "selected-row unselected-column 1T1C DAE"
    | .unselectedColumnStorageEndpoint =>
        .connectionLaw
          "selected-row unselected-column storage phase endpoint"
    | .unselectedColumnBitlineEndpoint =>
        .connectionLaw "unselected bitline phase endpoint"
  equation clause world observation _internal :=
    match clause with
    | .readEndpoint =>
        DramBankCoreReadBehavior profile world.readWorld
          observation.readPhase ()
    | .writeBusConnection =>
        DramTransmissionGateEquations
          (logicVoltage world.value) observation.writeBus
    | .selectedBitlineConnection =>
        DramTransmissionGateEquations observation.writeBus
          (observation.after.bitline world.column)
    | .selectedStorageEvolution =>
        if world.value then
          DramWriteBehavior
            (dramBankCoreSelectedWriteOneWorld
              profile world observation.readPhase)
            ⟨observation.selectedStorageTrace⟩ ()
        else
          Dram1T1CBehavior
            (dramBankCoreSelectedWriteZeroWorld
              profile world observation.readPhase)
            ⟨observation.selectedStorageTrace⟩ ()
    | .selectedStorageEndpoint =>
        observation.after.storage world.row world.column =
          observation.selectedStorageTrace dramBankCoreWriteHorizon
    | .unselectedStorageInitial =>
        ∀ row column,
          row ≠ world.row →
          observation.unselectedStorageTrace row column 0 =
            observation.readPhase.restored.storage row column
    | .unselectedStorageEvolution =>
        ∀ row column,
          row ≠ world.row →
          dram1T1CDAE.ACBehavesOn
            (dramBankCoreWriteUnselectedWorld
              profile observation.readPhase row column)
            1 (observation.unselectedStorageTrace row column)
    | .unselectedStorageEndpoint =>
        ∀ row column,
          row ≠ world.row →
          observation.after.storage row column =
            observation.unselectedStorageTrace row column 1
    | .unselectedColumnEvolution =>
        ∀ column, column ≠ world.column →
          if world.bits.bits world.row column then
            DramWriteBehavior
              (dramBankCoreWriteUnselectedColumnOneWorld
                profile world observation.readPhase column)
              ⟨observation.unselectedColumnTrace column⟩ ()
          else
            Dram1T1CBehavior
              (dramBankCoreWriteUnselectedColumnZeroWorld
                profile world observation.readPhase column)
              ⟨observation.unselectedColumnTrace column⟩ ()
    | .unselectedColumnStorageEndpoint =>
        ∀ column, column ≠ world.column →
          observation.after.storage world.row column =
            observation.unselectedColumnTrace column dramBankCoreWriteHorizon
    | .unselectedColumnBitlineEndpoint =>
        ∀ column, column ≠ world.column →
          DramTransmissionGateEquations
            (observation.readPhase.senseOutput column)
            (observation.after.bitline column)

noncomputable def DramBankCoreWriteBehavior
    (profile : DramBankCoreProfile rows columns) :
    Behavior (DramBankCoreWriteWorld rows columns)
      (DramBankCoreWriteObservation rows columns) Unit :=
  (DramBankCoreWriteProgram profile).behavior

theorem dramBankCoreWriteEquationManifest :
    EquationManifest
      (DramBankCoreWriteProgram
        (rows := rows) (columns := columns) profile)
      ["read endpoint phase"] := by
  constructor
  ·
    intro contract hcontract
    simp at hcontract
    subst contract
    exact ⟨.readEndpoint, rfl⟩
  ·
    intro contract hcontract
    rcases hcontract with ⟨clause, hclause⟩
    cases clause <;>
      simp [DramBankCoreWriteProgram] at hclause ⊢
    all_goals subst contract <;> simp

noncomputable def DramBankCoreWriteAllowed
    (profile : DramBankCoreProfile rows columns)
    (_world : DramBankCoreWriteWorld rows columns) : Prop :=
  DramBankCoreNominalProfile profile

noncomputable def dramBankCoreCanonicalWriteAfter
    (world : DramBankCoreWriteWorld rows columns)
    (readPhase : DramBankCoreReadObservation rows columns)
    (selectedStorageTrace : DenseTrace ℝ)
    (unselectedColumnTrace : Fin columns → DenseTrace ℝ) :
    DramArrayEndpoint rows columns where
  storage row column :=
    if row = world.row ∧ column = world.column then
      selectedStorageTrace dramBankCoreWriteHorizon
    else if row = world.row then
      unselectedColumnTrace column dramBankCoreWriteHorizon
    else
      readPhase.restored.storage row column
  bitline column :=
    if column = world.column then
      logicVoltage world.value
    else
      readPhase.restored.bitline column

/-- An unselected bitline remains connected to its sense output while another
column is written. Both endpoint connections are physical transmission-gate
relations. -/
theorem DramBankCoreWriteBehavior.unselected_bitline_preserved
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreWriteWorld rows columns}
    {observation : DramBankCoreWriteObservation rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (hbehavior :
      DramBankCoreWriteBehavior profile world observation ())
    (column : Fin columns) (hcolumn : column ≠ world.column) :
    observation.after.bitline column =
      observation.readPhase.restored.bitline column := by
  have hread := hbehavior .readEndpoint
  have hrestored :=
    hread.restored_selected_cell hprofile column
  have hafter :=
    dramTransmissionGate_correct
      (hbehavior .unselectedColumnBitlineEndpoint column hcolumn)
  have hsense := hread.sense_correct hprofile column
  calc
    observation.after.bitline column =
        observation.readPhase.senseOutput column := hafter
    _ = logicVoltage (world.bits.bits world.row column) := hsense
    _ = observation.readPhase.restored.bitline column := hrestored.2.symm

/-- Cells on unselected rows are in cutoff hold mode, so their storage voltage
is exactly preserved. Selected-row cells on other columns instead continue
their clamped restore trajectories and are covered by a logic-band theorem. -/
theorem DramBankCoreWriteBehavior.unselected_row_storage_preserved
    {profile : DramBankCoreProfile rows columns}
    {world : DramBankCoreWriteWorld rows columns}
    {observation : DramBankCoreWriteObservation rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (hbehavior :
      DramBankCoreWriteBehavior profile world observation ()) :
    ∀ row column, row ≠ world.row →
      observation.after.storage row column =
        observation.readPhase.restored.storage row column := by
  intro row column hrow
  have hinitial :=
    hbehavior .unselectedStorageInitial row column hrow
  have hevolution :=
    hbehavior .unselectedStorageEvolution row column hrow
  have hendpoint :=
    hbehavior .unselectedStorageEndpoint row column hrow
  have hconstant :=
    dram1T1CDAE.constant_on_of_residual_forces_zero hevolution
      (fun _time _storage derivative hresidual => by
        simpa [dram1T1CDAE, dram1T1CField,
          dramBankCoreWriteUnselectedWorld,
          deterministicWorld] using hresidual)
  calc
    observation.after.storage row column =
        observation.unselectedStorageTrace row column 1 :=
      hendpoint
    _ = observation.unselectedStorageTrace row column 0 :=
      hconstant 1 (by norm_num)
    _ = observation.readPhase.restored.storage row column :=
      hinitial

theorem dramBankCore_selected_write_realizable
    {profile : DramBankCoreProfile rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (world : DramBankCoreWriteWorld rows columns)
    (readPhase : DramBankCoreReadObservation rows columns)
    (hread :
      DramBankCoreReadBehavior profile world.readWorld readPhase ()) :
    ∃ trace,
      if world.value then
        DramWriteBehavior
          (dramBankCoreSelectedWriteOneWorld profile world readPhase)
          ⟨trace⟩ ()
      else
        Dram1T1CBehavior
          (dramBankCoreSelectedWriteZeroWorld profile world readPhase)
          ⟨trace⟩ () := by
  have hrestored :=
    hread.restored_selected_cell hprofile world.column
  simp only [DramBankCoreWriteWorld.readWorld] at hrestored
  have hbounds :=
    hread.restored_selected_storage_bounds hprofile world.column
  simp only [DramBankCoreWriteWorld.readWorld] at hbounds
  have hcell := hprofile.1 world.row world.column
  cases hvalue : world.value
  · have hadmissible :
        Dram1T1CAdmissible
          (dramBankCoreSelectedWriteZeroWorld profile world readPhase) := by
      simp only [Dram1T1CAdmissible,
        dramBankCoreSelectedWriteZeroWorld, deterministicWorld,
        hcell, nominalDramCellInstance, dramBankCoreWriteHorizon]
      refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_,
        by norm_num⟩
      · exact hbounds.1
      · linarith [hbounds.2]
    obtain ⟨boundary, _internal, hbehavior⟩ :=
      dram1T1C_realizable
        (dramBankCoreSelectedWriteZeroWorld profile world readPhase)
        hadmissible
    refine ⟨boundary.storageVoltage, ?_⟩
    simp only [hvalue, Bool.false_eq_true, ↓reduceIte]
    exact hbehavior
  · have hinitial :
        readPhase.restored.storage world.row world.column ≤ 4 := by
      exact hbounds.2
    obtain ⟨boundary, hbehavior⟩ :=
      nominalDramWriteOne_realizable
        hinitial (show 0 ≤ dramBankCoreWriteHorizon by
          norm_num [dramBankCoreWriteHorizon])
    refine ⟨boundary.storageVoltage, ?_⟩
    simp only [hvalue, ↓reduceIte]
    simpa [dramBankCoreSelectedWriteOneWorld,
      dramBankCoreWriteInstance, hcell, nominalDramCellInstance,
      nominalDramWriteOneWorld, deterministicWorld] using hbehavior

theorem dramBankCore_unselected_column_realizable
    {profile : DramBankCoreProfile rows columns}
    (hprofile : DramBankCoreNominalProfile profile)
    (world : DramBankCoreWriteWorld rows columns)
    (readPhase : DramBankCoreReadObservation rows columns)
    (hread :
      DramBankCoreReadBehavior profile world.readWorld readPhase ())
    (column : Fin columns) :
    ∃ trace,
      if world.bits.bits world.row column then
        DramWriteBehavior
          (dramBankCoreWriteUnselectedColumnOneWorld
            profile world readPhase column)
          ⟨trace⟩ ()
      else
        Dram1T1CBehavior
          (dramBankCoreWriteUnselectedColumnZeroWorld
            profile world readPhase column)
          ⟨trace⟩ () := by
  have hbounds :=
    hread.restored_selected_storage_bounds hprofile column
  simp only [DramBankCoreWriteWorld.readWorld] at hbounds
  cases hbit : world.bits.bits world.row column
  · have hadmissible :
        Dram1T1CAdmissible
          (dramBankCoreWriteUnselectedColumnZeroWorld
            profile world readPhase column) := by
      rw [dramBankCore_unselected_column_zero_world_eq_nominal
        hprofile world readPhase column]
      simp only [Dram1T1CAdmissible,
        nominalDramBankCoreWriteZeroWorld, deterministicWorld,
        dramBankCoreWriteHorizon]
      exact ⟨by norm_num, by norm_num, by norm_num, by norm_num,
        hbounds.1, by linarith [hbounds.2], by norm_num⟩
    obtain ⟨boundary, _internal, hbehavior⟩ :=
      dram1T1C_realizable
        (dramBankCoreWriteUnselectedColumnZeroWorld
          profile world readPhase column)
        hadmissible
    refine ⟨boundary.storageVoltage, ?_⟩
    rw [if_neg (by simpa using hbit)]
    exact hbehavior
  · obtain ⟨boundary, hbehavior⟩ :=
      nominalDramWriteOne_realizable hbounds.2
        (show 0 ≤ dramBankCoreWriteHorizon by
          norm_num [dramBankCoreWriteHorizon])
    refine ⟨boundary.storageVoltage, ?_⟩
    simp
    rw [dramBankCore_unselected_column_one_world_eq_nominal
      hprofile world readPhase hread column hbit]
    exact hbehavior

theorem dramBankCore_write_realizable
    (profile : DramBankCoreProfile rows columns) :
    RealizableUnder (DramBankCoreWriteBehavior profile)
      (DramBankCoreWriteAllowed profile) := by
  intro world hprofile
  obtain ⟨readPhase, _readInternal, hread⟩ :=
    dramBankCore_read_realizable profile world.readWorld hprofile
  obtain ⟨selectedStorageTrace, hselected⟩ :=
    dramBankCore_selected_write_realizable hprofile world readPhase hread
  have hunselectedExists :
      ∀ column, ∃ trace,
        if world.bits.bits world.row column then
          DramWriteBehavior
            (dramBankCoreWriteUnselectedColumnOneWorld
              profile world readPhase column)
            ⟨trace⟩ ()
        else
          Dram1T1CBehavior
            (dramBankCoreWriteUnselectedColumnZeroWorld
              profile world readPhase column)
            ⟨trace⟩ () :=
    fun column =>
      dramBankCore_unselected_column_realizable
        hprofile world readPhase hread column
  let unselectedColumnTrace : Fin columns → DenseTrace ℝ :=
    fun column => Classical.choose (hunselectedExists column)
  have hunselectedBehavior :
      ∀ column,
        if world.bits.bits world.row column then
          DramWriteBehavior
            (dramBankCoreWriteUnselectedColumnOneWorld
              profile world readPhase column)
            ⟨unselectedColumnTrace column⟩ ()
        else
          Dram1T1CBehavior
            (dramBankCoreWriteUnselectedColumnZeroWorld
              profile world readPhase column)
            ⟨unselectedColumnTrace column⟩ () :=
    fun column => Classical.choose_spec (hunselectedExists column)
  let observation : DramBankCoreWriteObservation rows columns :=
    { readPhase
      writeBus := logicVoltage world.value
      selectedStorageTrace
      unselectedStorageTrace := fun row column _time =>
        readPhase.restored.storage row column
      unselectedColumnTrace
      after :=
        dramBankCoreCanonicalWriteAfter
          world readPhase selectedStorageTrace unselectedColumnTrace }
  refine ⟨observation, (), ?_⟩
  dsimp [DramBankCoreWriteBehavior, DramBankCoreWriteProgram,
    EquationProgram.behavior]
  intro clause
  cases clause
  case readEndpoint =>
    exact hread
  case writeBusConnection =>
    change DramTransmissionGateEquations
      (logicVoltage world.value) (logicVoltage world.value)
    cases world.value <;>
      apply dramTransmissionGate_realizable <;> simp [logicVoltage]
  case selectedBitlineConnection =>
    cases hvalue : world.value <;>
      simp [observation, dramBankCoreCanonicalWriteAfter, hvalue] <;>
      apply dramTransmissionGate_realizable <;> simp [logicVoltage]
  case selectedStorageEvolution =>
    simpa [observation] using hselected
  case selectedStorageEndpoint =>
    simp [observation, dramBankCoreCanonicalWriteAfter]
  case unselectedStorageInitial =>
    intro row column hrow
    rfl
  case unselectedStorageEvolution =>
    intro row column hrow
    exact dram1T1C_hold_dae_realizable rfl
      (by simp [dramBankCoreWriteUnselectedWorld, deterministicWorld])
  case unselectedStorageEndpoint =>
    intro row column hrow
    have hnot :
        ¬(row = world.row ∧ column = world.column) := by
      intro hselected
      exact hrow hselected.1
    simp [observation, dramBankCoreCanonicalWriteAfter, hnot, hrow]
  case unselectedColumnEvolution =>
    intro column hcolumn
    simpa [observation] using hunselectedBehavior column
  case unselectedColumnStorageEndpoint =>
    intro column hcolumn
    simp [observation, dramBankCoreCanonicalWriteAfter, hcolumn]
  case unselectedColumnBitlineEndpoint =>
    intro column hcolumn
    have hrestored :=
      (show DramBankCoreReadBehavior profile world.readWorld readPhase ()
        from hread).restored_selected_cell hprofile column
    have hsense :=
      (show DramBankCoreReadBehavior profile world.readWorld readPhase ()
        from hread).sense_correct hprofile column
    have heq :
        observation.after.bitline column =
          observation.readPhase.senseOutput column := by
      simpa [observation, dramBankCoreCanonicalWriteAfter, hcolumn,
        DramBankCoreWriteWorld.readWorld] using hrestored.2.trans hsense.symm
    rw [heq]
    apply dramTransmissionGate_realizable
    · rw [hsense]
      simp only [DramBankCoreWriteWorld.readWorld]
      cases world.bits.bits world.row column <;> simp [logicVoltage]
    · rw [hsense]
      simp only [DramBankCoreWriteWorld.readWorld]
      cases world.bits.bits world.row column <;> simp [logicVoltage]

end LeanModels.Spice
