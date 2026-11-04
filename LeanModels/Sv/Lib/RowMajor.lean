import LeanModels.Sv.CombViewArith

/-!
# `LeanModels.Sv.Lib.RowMajor`: row-major offsets at natural coordinates

`sv_equations` states the rows of a generate family's two-dimensional array through `CombView.rmN W i j` (the
row-major offset `i * W + j`, at `Int` coordinates clamped at `0`). At coordinates that are casts of natural numbers
these are the plain `Nat` offsets: row `i` column `0` (`rmN_row0`), row `i + 1` column `0` (`rmN_succ0`), the last
column `W - 1` of row `i` (`rmN_last_col`), each in the form `sv_equations` prints it, and any cell given by equations
for its width, row and column (`rmN_eq`).
-/

namespace LeanModels.Sv.Lib

open LeanModels.Sv.CombView

/-- Row `i`, column `0` (printed `rmN ↑P ↑i 0`): offset `i * P`. -/
theorem rmN_row0 (P i : Nat) : rmN (P : Int) (i : Int) 0 = i * P := by
  have h1 : (i : Int).toNat = i := by omega
  have h2 : (P : Int).toNat = P := by omega
  unfold rmN
  rw [h1, h2]; rfl

/-- Row `i + 1`, column `0` (printed `rmN ↑P (↑i + 1) 0`): offset `(i + 1) * P`. -/
theorem rmN_succ0 (P i : Nat) : rmN (P : Int) ((i : Int) + 1) 0 = (i + 1) * P := by
  have h1 : ((i : Int) + 1).toNat = i + 1 := by omega
  have h2 : (P : Int).toNat = P := by omega
  unfold rmN
  rw [h1, h2]; rfl

/-- The last column `P - 1` of row `i` (printed `rmN ↑P ↑i (↑P + -1)`), `P ≥ 1`: offset `i * P + (P - 1)`. -/
theorem rmN_last_col (P i : Nat) (hP : 1 ≤ P) : rmN (P : Int) (i : Int) ((P : Int) + -1) = i * P + (P - 1) := by
  have h1 : (i : Int).toNat = i := by omega
  have h2 : (P : Int).toNat = P := by omega
  have h3 : ((P : Int) + -1).toNat = P - 1 := by omega
  unfold rmN
  rw [h1, h2, h3]

/-- Any cell, given by equations for its width, row and column: offset `r * w + c`. -/
theorem rmN_eq (wI i j : Int) (w r c : Nat) (hw : wI = (w : Int)) (hi : i = (r : Int)) (hj : j = (c : Int)) :
    rmN wI i j = r * w + c := by
  unfold rmN
  rw [hw, hi, hj]
  simp

end LeanModels.Sv.Lib
