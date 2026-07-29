import Examples.spice.dram_array_2x2.proof

open LeanModels.Circuit LeanModels.Spice
open Examples.spice.dram_array_2x2.proof

theorem dram_array_2x2_layout :
    dramArray2x2.toDramArray2x2 = .ok dramArrayLayout := by proofs

theorem dram_array_2x2_projection_is_ok :
    (dramArray2x2.toDramArray2x2).isOk = true := by proofs

theorem dram_array_2x2_source_parameters :
    dramArrayLayout.threshold = 1 ∧
    dramArrayLayout.beta = 1 / 10000 ∧
    (∀ row column,
      (dramArrayLayout.cells row column).storageCapacitance =
        3 / 100000000000000) ∧
    (∀ column,
      dramArrayLayout.bitlineCapacitances column =
        3 / 10000000000000) := by proofs

theorem dram_array_2x2_shared_topology :
    (∀ row column,
      (dramArrayLayout.cells row column).wordlineNode =
        dramArrayLayout.wordlines row) ∧
    (∀ row column,
      (dramArrayLayout.cells row column).bitlineNode =
        dramArrayLayout.bitlines column) := by proofs

theorem dram_array_cell00_parameters :
    dramArrayCell00.threshold = 1 ∧
    dramArrayCell00.beta = 1 / 10000 ∧
    dramArrayCell00.storageCapacitance =
      3 / 100000000000000 ∧
    dramArrayCell00.bitlineCapacitance =
      3 / 10000000000000 := by proofs

theorem dram_array_cell_program_physics_only :
    DramCellProgram.PhysicsOnly := by proofs

theorem dram_array_cell00_hold_realizable :
    ∃ boundary,
      DramCellBehavior dramArrayCell00HoldWorld boundary () := by proofs

theorem dram_array_cell00_charge_conserved
    {boundary : DramCellBoundary}
    (hbehavior :
      DramCellBehavior dramArrayCell00HoldWorld boundary ()) :
    ∀ time ∈ Set.Icc 0
        dramArrayCell00HoldWorld.environment.horizon,
      dramCellTotalCharge dramArrayCell00 (boundary.voltage time) =
        dramCellTotalCharge dramArrayCell00 (boundary.voltage 0) := by proofs

theorem dram_array_read_zero_shared_voltage :
    dramCellSharedVoltage dramArrayCell00 dramArrayReadZeroBefore =
      25 / 11 := by proofs

theorem dram_array_read_one_shared_voltage :
    dramCellSharedVoltage dramArrayCell00 dramArrayReadOneBefore =
      29 / 11 := by proofs

theorem dram_array_read_zero_from_physics
    {after : DramCellEndpoint}
    (hcharge :
      DramCellChargeConserved dramArrayCell00
        dramArrayReadZeroBefore after)
    (hsettled : DramCellChannelSettled after) :
    after.storage = 25 / 11 ∧ after.bitline = 25 / 11 := by proofs

theorem dram_array_read_one_from_physics
    {after : DramCellEndpoint}
    (hcharge :
      DramCellChargeConserved dramArrayCell00
        dramArrayReadOneBefore after)
    (hsettled : DramCellChannelSettled after) :
    after.storage = 29 / 11 ∧ after.bitline = 29 / 11 := by proofs

theorem dram_array_settled_read_realizable (stored : Bool) :
    ∃ after,
      DramCellSettledRead dramArrayCell00
        (if stored then dramArrayReadOneBefore
          else dramArrayReadZeroBefore)
        after := by proofs

theorem dram_array_unboosted_write_one_target :
    dramCellWriteOneTarget 5 5 dramArrayCell00.threshold = 4 := by proofs

theorem dram_array_boosted_write_one_target :
    dramCellWriteOneTarget 5 6 dramArrayCell00.threshold = 5 := by proofs

theorem dram_array_cell_instances_equal
    (row column : Fin 2) :
    dramArrayLayout.cellInstance row column = dramArrayCell00 := by proofs

theorem dram_array_row0_activation_realizable :
    ∃ after,
      DramArrayRowActivated dramArrayLayout 0 dramArrayBefore after := by proofs

theorem dram_array_row0_activation_correct
    {after : DramArrayEndpoint 2 2}
    (hactivation :
      DramArrayRowActivated dramArrayLayout 0 dramArrayBefore after) :
    after.bitline 0 = 29 / 11 ∧
    after.bitline 1 = 25 / 11 ∧
    (∀ column, after.storage 1 column = dramArrayBefore.storage 1 column) :=
  by proofs

#print axioms dram_array_2x2_layout
#print axioms dram_array_2x2_projection_is_ok
#print axioms dram_array_2x2_source_parameters
#print axioms dram_array_2x2_shared_topology
#print axioms dram_array_cell00_parameters
#print axioms dram_array_cell_program_physics_only
#print axioms dram_array_cell00_hold_realizable
#print axioms dram_array_cell00_charge_conserved
#print axioms dram_array_read_zero_from_physics
#print axioms dram_array_read_one_from_physics
#print axioms dram_array_settled_read_realizable
#print axioms dram_array_unboosted_write_one_target
#print axioms dram_array_boosted_write_one_target
#print axioms dram_array_cell_instances_equal
#print axioms dram_array_row0_activation_realizable
#print axioms dram_array_row0_activation_correct
