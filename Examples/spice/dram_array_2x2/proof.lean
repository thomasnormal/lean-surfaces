import LeanModels.Spice.DramArrayContract
import LeanModels.Circuit.Surface
import LeanModels.Python.Surface

namespace Examples.spice.dram_array_2x2.proof

open LeanModels.Circuit LeanModels.Spice

load_circuit dramArray2x2 from
  "Examples/spice/dram_array_2x2/dram_array_2x2.cir"

def dramArrayExpectedLayout : DramArrayLayout 2 2 :=
  let cell00 : DramCellLayout :=
    ⟨⟨6⟩, ⟨2⟩, ⟨3⟩, ⟨7⟩, ⟨0⟩, ⟨0⟩,
      3 / 100000000000000⟩
  let cell01 : DramCellLayout :=
    ⟨⟨7⟩, ⟨3⟩, ⟨4⟩, ⟨7⟩, ⟨2⟩, ⟨0⟩,
      3 / 100000000000000⟩
  let cell10 : DramCellLayout :=
    ⟨⟨8⟩, ⟨4⟩, ⟨5⟩, ⟨8⟩, ⟨0⟩, ⟨0⟩,
      3 / 100000000000000⟩
  let cell11 : DramCellLayout :=
    ⟨⟨9⟩, ⟨5⟩, ⟨6⟩, ⟨8⟩, ⟨2⟩, ⟨0⟩,
      3 / 100000000000000⟩
  { cells := fun row column =>
      selectFin2
        (selectFin2 cell00 cell01 column)
        (selectFin2 cell10 cell11 column)
        row
    wordlines := selectFin2 ⟨7⟩ ⟨8⟩
    bitlines := selectFin2 ⟨0⟩ ⟨2⟩
    bitlineCapacitors := selectFin2 ⟨0⟩ ⟨1⟩
    bitlineCapacitances :=
      selectFin2 (3 / 10000000000000) (3 / 10000000000000)
    threshold := 1
    beta := 1 / 10000 }

def dramArrayLayout : DramArrayLayout 2 2 :=
  match dramArray2x2.toDramArray2x2 with
  | .ok layout => layout
  | .error _ => default

theorem dram_array_2x2_projection :
    dramArray2x2.toDramArray2x2 = .ok dramArrayExpectedLayout := by
  norm_num [LeanModels.Circuit.ElaboratedCircuit.toDramArray2x2,
    LeanModels.Spice.ElaboratedCircuit.toDramArray2x2,
    LeanModels.Circuit.NodeId.beq_mk,
    LeanModels.Circuit.ModelId.beq_mk,
    bne,
    dramArray2x2, dramArrayExpectedLayout]

theorem dram_array_2x2_projection_is_ok :
    (dramArray2x2.toDramArray2x2).isOk = true := by
  rw [dram_array_2x2_projection]
  rfl

theorem dram_array_2x2_layout :
    dramArray2x2.toDramArray2x2 = .ok dramArrayLayout := by
  unfold dramArrayLayout
  rw [dram_array_2x2_projection]

theorem dramArrayLayout_eq :
    dramArrayLayout = dramArrayExpectedLayout := by
  unfold dramArrayLayout
  rw [dram_array_2x2_projection]

theorem dram_array_2x2_source_parameters :
    dramArrayLayout.threshold = 1 ∧
    dramArrayLayout.beta = 1 / 10000 ∧
    (∀ row column,
      (dramArrayLayout.cells row column).storageCapacitance =
        3 / 100000000000000) ∧
    (∀ column,
      dramArrayLayout.bitlineCapacitances column =
        3 / 10000000000000) := by
  rw [dramArrayLayout_eq]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro row column
    fin_cases row <;> fin_cases column <;>
      norm_num [dramArrayExpectedLayout, selectFin2]
  · intro column
    fin_cases column <;>
      norm_num [dramArrayExpectedLayout, selectFin2]

theorem dram_array_2x2_shared_topology :
    (∀ row column,
      (dramArrayLayout.cells row column).wordlineNode =
        dramArrayLayout.wordlines row) ∧
    (∀ row column,
      (dramArrayLayout.cells row column).bitlineNode =
        dramArrayLayout.bitlines column) := by
  rw [dramArrayLayout_eq]
  constructor <;>
    intro row column <;>
    fin_cases row <;> fin_cases column <;>
      simp [dramArrayExpectedLayout, selectFin2]

noncomputable def dramArrayCell00 : DramCellInstance :=
  dramArrayLayout.cellInstance 0 0

theorem dram_array_cell00_parameters :
    dramArrayCell00.threshold = 1 ∧
    dramArrayCell00.beta = 1 / 10000 ∧
    dramArrayCell00.storageCapacitance =
      3 / 100000000000000 ∧
    dramArrayCell00.bitlineCapacitance =
      3 / 10000000000000 := by
  unfold dramArrayCell00
  rw [dramArrayLayout_eq]
  norm_num [DramArrayLayout.cellInstance,
    dramArrayExpectedLayout, selectFin2]

noncomputable def dramArrayCell00HoldWorld : DramCellWorld :=
  deterministicWorld dramArrayCell00
    { wordlineVoltage := 0
      initialStorage := 4
      initialBitline := 5 / 2
      horizon := 1 / 1000000000 }

theorem dram_array_cell_program_physics_only :
    DramCellProgram.PhysicsOnly :=
  dramCellProgram_physicsOnly

theorem dram_array_cell00_hold_realizable :
    ∃ boundary,
      DramCellBehavior dramArrayCell00HoldWorld boundary () := by
  apply dramCell_hold_realizable dramArrayCell00HoldWorld
  · unfold dramArrayCell00HoldWorld dramArrayCell00
    rw [dramArrayLayout_eq]
    norm_num [DramCellAdmissible, DramArrayLayout.cellInstance,
      dramArrayExpectedLayout, selectFin2, deterministicWorld]
  · rfl
  · norm_num [dramArrayCell00HoldWorld, deterministicWorld]
  · norm_num [dramArrayCell00HoldWorld, deterministicWorld]

theorem dram_array_cell00_charge_conserved
    {boundary : DramCellBoundary}
    (hbehavior :
      DramCellBehavior dramArrayCell00HoldWorld boundary ()) :
    ∀ time ∈ Set.Icc 0
        dramArrayCell00HoldWorld.environment.horizon,
      dramCellTotalCharge dramArrayCell00 (boundary.voltage time) =
        dramCellTotalCharge dramArrayCell00 (boundary.voltage 0) :=
  dramCell_behavior_conserves_charge hbehavior

noncomputable def dramArrayReadZeroBefore : DramCellEndpoint :=
  { storage := 0, bitline := 5 / 2 }

noncomputable def dramArrayReadOneBefore : DramCellEndpoint :=
  { storage := 4, bitline := 5 / 2 }

theorem dram_array_read_zero_shared_voltage :
    dramCellSharedVoltage dramArrayCell00 dramArrayReadZeroBefore =
      25 / 11 := by
  unfold dramArrayCell00
  rw [dramArrayLayout_eq]
  norm_num [dramCellSharedVoltage, dramCellEndpointCharge,
    DramArrayLayout.cellInstance,
    dramArrayExpectedLayout, dramArrayReadZeroBefore, selectFin2]

/-- The high cell starts at 4 V, not 5 V: an unboosted NMOS wordline loses
one source-derived threshold volt. -/
theorem dram_array_read_one_shared_voltage :
    dramCellSharedVoltage dramArrayCell00 dramArrayReadOneBefore =
      29 / 11 := by
  unfold dramArrayCell00
  rw [dramArrayLayout_eq]
  norm_num [dramCellSharedVoltage, dramCellEndpointCharge,
    DramArrayLayout.cellInstance,
    dramArrayExpectedLayout, dramArrayReadOneBefore, selectFin2]

theorem dram_array_read_zero_from_physics
    {after : DramCellEndpoint}
    (hcharge :
      DramCellChargeConserved dramArrayCell00
        dramArrayReadZeroBefore after)
    (hsettled : DramCellChannelSettled after) :
    after.storage = 25 / 11 ∧ after.bitline = 25 / 11 := by
  have hparameters := dram_array_cell00_parameters
  have hderived := dramCell_shared_voltage
    (device := dramArrayCell00)
    (before := dramArrayReadZeroBefore) (after := after)
    (by linarith [hparameters.2.2.1])
    (by linarith [hparameters.2.2.2]) hcharge hsettled
  simpa [dram_array_read_zero_shared_voltage] using hderived

theorem dram_array_read_one_from_physics
    {after : DramCellEndpoint}
    (hcharge :
      DramCellChargeConserved dramArrayCell00
        dramArrayReadOneBefore after)
    (hsettled : DramCellChannelSettled after) :
    after.storage = 29 / 11 ∧ after.bitline = 29 / 11 := by
  have hparameters := dram_array_cell00_parameters
  have hderived := dramCell_shared_voltage
    (device := dramArrayCell00)
    (before := dramArrayReadOneBefore) (after := after)
    (by linarith [hparameters.2.2.1])
    (by linarith [hparameters.2.2.2]) hcharge hsettled
  simpa [dram_array_read_one_shared_voltage] using hderived

theorem dram_array_settled_read_realizable (stored : Bool) :
    ∃ after,
      DramCellSettledRead dramArrayCell00
        (if stored then dramArrayReadOneBefore
          else dramArrayReadZeroBefore)
        after := by
  apply dramCell_settled_read_realizable
  have hparameters := dram_array_cell00_parameters
  linarith [hparameters.2.2.1, hparameters.2.2.2]

theorem dram_array_unboosted_write_one_target :
    dramCellWriteOneTarget 5 5 dramArrayCell00.threshold = 4 := by
  rw [dram_array_cell00_parameters.1]
  norm_num [dramCellWriteOneTarget]

theorem dram_array_boosted_write_one_target :
    dramCellWriteOneTarget 5 6 dramArrayCell00.threshold = 5 := by
  rw [dram_array_cell00_parameters.1]
  norm_num [dramCellWriteOneTarget]

theorem dram_array_cell_instances_equal
    (row column : Fin 2) :
    dramArrayLayout.cellInstance row column = dramArrayCell00 := by
  unfold dramArrayCell00
  rw [dramArrayLayout_eq]
  fin_cases row <;> fin_cases column <;>
    norm_num [DramArrayLayout.cellInstance,
      dramArrayExpectedLayout, selectFin2]

noncomputable def dramArrayBefore : DramArrayEndpoint 2 2 where
  storage row column :=
    selectFin2 (selectFin2 4 0 column) (selectFin2 0 4 column) row
  bitline _column := 5 / 2

theorem dram_array_before_row0_cell0 :
    dramArrayBefore.cell 0 0 = dramArrayReadOneBefore := by
  rfl

theorem dram_array_before_row0_cell1 :
    dramArrayBefore.cell 0 1 = dramArrayReadZeroBefore := by
  rfl

theorem dram_array_row0_activation_realizable :
    ∃ after,
      DramArrayRowActivated dramArrayLayout 0 dramArrayBefore after := by
  apply dramArray_row_activation_realizable
  intro column
  rw [dram_array_cell_instances_equal 0 column]
  have hparameters := dram_array_cell00_parameters
  linarith [hparameters.2.2.1, hparameters.2.2.2]

/-- Row activation shares charge on both columns at once.  The selected
column may be sensed later; the other activated column must still be
restored.  Every storage node on the unselected row is preserved. -/
theorem dram_array_row0_activation_correct
    {after : DramArrayEndpoint 2 2}
    (hactivation :
      DramArrayRowActivated dramArrayLayout 0 dramArrayBefore after) :
    after.bitline 0 = 29 / 11 ∧
    after.bitline 1 = 25 / 11 ∧
    (∀ column, after.storage 1 column = dramArrayBefore.storage 1 column) := by
  have hparameters := dram_array_cell00_parameters
  have hcolumn0 := hactivation.selected_column 0
    (by
      rw [dram_array_cell_instances_equal 0 0]
      linarith [hparameters.2.2.1])
    (by
      rw [dram_array_cell_instances_equal 0 0]
      linarith [hparameters.2.2.2])
  have hcolumn1 := hactivation.selected_column 1
    (by
      rw [dram_array_cell_instances_equal 0 1]
      linarith [hparameters.2.2.1])
    (by
      rw [dram_array_cell_instances_equal 0 1]
      linarith [hparameters.2.2.2])
  constructor
  · rw [dram_array_cell_instances_equal 0 0,
      dram_array_before_row0_cell0,
      dram_array_read_one_shared_voltage] at hcolumn0
    exact hcolumn0.2
  constructor
  · rw [dram_array_cell_instances_equal 0 1,
      dram_array_before_row0_cell1,
      dram_array_read_zero_shared_voltage] at hcolumn1
    exact hcolumn1.2
  · intro column
    exact hactivation.unselected_storage_preserved (by decide) column

end Examples.spice.dram_array_2x2.proof
