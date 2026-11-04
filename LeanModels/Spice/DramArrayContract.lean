import LeanModels.Spice.DramCell

/-!
# Compositional DRAM row-activation contract

Activating a wordline connects every cell in that row to its column bitline.
The contract below is assembled from the physical settled-cell contract.  It
does not treat a 2x2 array as four independent reads: all columns on the
selected row share charge simultaneously, while every unselected-row storage
node is preserved.
-/

namespace LeanModels.Spice

structure DramArrayEndpoint (rows columns : Nat) where
  storage : Fin rows → Fin columns → ℝ
  bitline : Fin columns → ℝ

def DramArrayEndpoint.cell
    (state : DramArrayEndpoint rows columns)
    (row : Fin rows) (column : Fin columns) : DramCellEndpoint :=
  { storage := state.storage row column
    bitline := state.bitline column }

def DramArrayRowActivated
    (layout : DramArrayLayout rows columns)
    (selectedRow : Fin rows)
    (before after : DramArrayEndpoint rows columns) : Prop :=
  (∀ column,
    DramCellSettledRead (layout.cellInstance selectedRow column)
      (before.cell selectedRow column)
      (after.cell selectedRow column)) ∧
  (∀ row, row ≠ selectedRow →
    ∀ column, after.storage row column = before.storage row column)

noncomputable def dramArrayActivatedEndpoint
    (layout : DramArrayLayout rows columns)
    (selectedRow : Fin rows)
    (before : DramArrayEndpoint rows columns) :
    DramArrayEndpoint rows columns where
  storage row column :=
    if row = selectedRow then
      dramCellSharedVoltage (layout.cellInstance selectedRow column)
        (before.cell selectedRow column)
    else
      before.storage row column
  bitline column :=
    dramCellSharedVoltage (layout.cellInstance selectedRow column)
      (before.cell selectedRow column)

theorem dramArray_row_activation_realizable
    (layout : DramArrayLayout rows columns)
    (selectedRow : Fin rows)
    (before : DramArrayEndpoint rows columns)
    (hcapacitance :
      ∀ column,
        (layout.cellInstance selectedRow column).storageCapacitance +
          (layout.cellInstance selectedRow column).bitlineCapacitance ≠ 0) :
    ∃ after, DramArrayRowActivated layout selectedRow before after := by
  let after := dramArrayActivatedEndpoint layout selectedRow before
  refine ⟨after, ?_, ?_⟩
  · intro column
    have hcell :=
      dramCell_shared_endpoint_correct
        (layout.cellInstance selectedRow column)
        (before.cell selectedRow column)
        (hcapacitance column)
    simpa [after, dramArrayActivatedEndpoint, DramArrayEndpoint.cell,
      dramCellSharedEndpoint] using hcell
  · intro row hrow column
    simp [after, dramArrayActivatedEndpoint, hrow]

theorem DramArrayRowActivated.unselected_storage_preserved
    {layout : DramArrayLayout rows columns}
    {selectedRow : Fin rows}
    {before after : DramArrayEndpoint rows columns}
    (hactivation :
      DramArrayRowActivated layout selectedRow before after)
    {row : Fin rows} (hrow : row ≠ selectedRow)
    (column : Fin columns) :
    after.storage row column = before.storage row column :=
  hactivation.2 row hrow column

theorem DramArrayRowActivated.selected_column
    {layout : DramArrayLayout rows columns}
    {selectedRow : Fin rows}
    {before after : DramArrayEndpoint rows columns}
    (hactivation :
      DramArrayRowActivated layout selectedRow before after)
    (column : Fin columns)
    (hstorageCap :
      0 <
        (layout.cellInstance selectedRow column).storageCapacitance)
    (hbitlineCap :
      0 <
        (layout.cellInstance selectedRow column).bitlineCapacitance) :
    after.storage selectedRow column =
        dramCellSharedVoltage
          (layout.cellInstance selectedRow column)
          (before.cell selectedRow column) ∧
      after.bitline column =
        dramCellSharedVoltage
          (layout.cellInstance selectedRow column)
          (before.cell selectedRow column) := by
  exact dramCell_shared_voltage hstorageCap hbitlineCap
    (hactivation.1 column).1 (hactivation.1 column).2

end LeanModels.Spice
