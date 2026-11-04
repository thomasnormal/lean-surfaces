import LeanModels.Sv.Known2
import LeanModels.Sv.Comb2Base

/-!
# A flat memory read as an array (`run2` bridge for the D7 array view)

**Status: provisional over `run2`** (library, never trusted). Imported by nothing in the tree.

`run2` (Design2) keeps an unpacked memory `logic [W-1:0] mem [0:2^A-1]` as ONE `2^A * W`-bit vector,
read and written by dynamic element selects. This module relates that vector to the array view D7,
a `Fin (2^A)`-indexed store of words:
* `rfRead`/`rfWrite` are `evalExpr2`'s dynamic-index read and the NBA index write;
* `arrRead`/`arrWrite` are their array twins;
* `Abs` says the vector represents the array;
* `rfRead_eq` and `rfWrite_abs` are the bridge; `eval_index` evaluates a dynamic read.

Moved unchanged from `svgolf/design/architecture/RegFile.lean` (lead's ruling, 2026-11-02: under E
arrays are array-valued state natively, so this bridge is `run2`-specific and is not generalized
further).
-/

namespace LeanModels.Sv.FlatMem

open LeanModels.Sv

/-- The read port's value: word `raddr` of `mem`; `x` for an unknown or out-of-range address. -/
def rfRead (W : Nat) (mem ra : LVec) : LVec :=
  match ra.toNat? with
  | some i => if (i + 1) * W ≤ mem.width then mem.extract (i * W) W else LVec.xVec W
  | none => LVec.xVec W

/-- The memory after the edge: word `waddr` written when `we` is true. -/
def rfWrite (W : Nat) (mem we wa wd : LVec) : LVec :=
  if we.condTrue then
    match wa.toNat? with
    | some i => if (i + 1) * W ≤ mem.width then mem.insertAt (i * W) (wd.resizeU W) else mem
    | none => mem
  else mem

theorem rfRead_width (W : Nat) (mem ra : LVec) : (rfRead W mem ra).width = W := by
  unfold rfRead
  split
  · split <;> simp
  · simp

theorem resizeU_of_width {v : LVec} {w : Nat} (h : v.width = w) : v.resizeU w = v := by
  subst h
  apply LVec.ext_getElem?
  intro i
  simp only [LVec.resizeU, Array.getElem?_ofFn, LVec.width]
  by_cases hi : i < v.bits.size <;> simp [hi]

/-- A dynamic element read of one signal by another is `rfRead`. -/
theorem eval_index {F W : Nat} (hF : 2 ≤ F) {st : SvState} {m r : String} {mem ra : LVec}
    (hm : SvState.lookup st m = some mem) (hr : SvState.lookup st r = some ra) :
    evalExpr2 F st (.index (.ident m) (.ident r) W) = .ok (rfRead W mem ra) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 2 := ⟨F - 2, by omega⟩
  simp only [evalExpr2, readSignal, hm, hr, Res.ok_bind]
  unfold rfRead
  cases ra.toNat? with
  | none => rfl
  | some i => dsimp only; split <;> rfl

/-- **Array read** on a `Fin (2^A)`-indexed store: the word at a known in-range address, else `x`. -/
def arrRead {A : Nat} (W : Nat) (s : Fin (2 ^ A) → LVec) (ra : LVec) : LVec :=
  match ra.toNat? with
  | some i => if h : i < 2 ^ A then s ⟨i, h⟩ else LVec.xVec W
  | none => LVec.xVec W

/-- **Array write**: when `we` is true, the word at a known in-range address. -/
def arrWrite {A : Nat} (W : Nat) (s : Fin (2 ^ A) → LVec) (we wa wd : LVec) : Fin (2 ^ A) → LVec :=
  if we.condTrue then
    match wa.toNat? with
    | some i => if h : i < 2 ^ A then (fun j => if j = ⟨i, h⟩ then wd.resizeU W else s j) else s
    | none => s
  else s

/-- The flat memory represents the array: the right width, and word `j` is `s j`. -/
def Abs (A W : Nat) (mem : LVec) (s : Fin (2 ^ A) → LVec) : Prop :=
  mem.width = 2 ^ A * W ∧ ∀ j : Fin (2 ^ A), mem.extract (j.val * W) W = s j

theorem in_range {A W i : Nat} (hW : 1 ≤ W) : (i + 1) * W ≤ 2 ^ A * W ↔ i < 2 ^ A := by
  rw [Nat.mul_le_mul_right_iff (by omega)]; omega

theorem rfRead_eq {A W : Nat} (hW : 1 ≤ W) {mem : LVec} {s : Fin (2 ^ A) → LVec}
    (h : Abs A W mem s) (ra : LVec) : rfRead W mem ra = arrRead W s ra := by
  unfold rfRead arrRead
  cases ra.toNat? with
  | none => rfl
  | some i =>
      simp only [h.1, in_range hW]
      split
      · rename_i hi; exact h.2 ⟨i, hi⟩
      · rfl

theorem rfWrite_abs {A W : Nat} (hW : 1 ≤ W) {mem : LVec} {s : Fin (2 ^ A) → LVec}
    (h : Abs A W mem s) (we wa wd : LVec) :
    Abs A W (rfWrite W mem we wa wd) (arrWrite W s we wa wd) := by
  unfold rfWrite arrWrite
  by_cases hwe : we.condTrue = true
  · simp only [hwe, if_true]
    cases wa.toNat? with
    | none => exact h
    | some i =>
        simp only [h.1, in_range hW]
        split
        · rename_i hi
          refine ⟨by simp [h.1], fun j => ?_⟩
          by_cases hj : j = ⟨i, hi⟩
          · subst hj
            dsimp only
            rw [if_pos rfl]
            have hle := (in_range (A := A) hW).mpr hi
            rw [Nat.add_mul, Nat.one_mul] at hle
            exact LVec.extract_insertAt_self (by simp) (by rw [h.1]; exact hle)
          · dsimp only
            rw [if_neg hj, ← h.2 j]
            have hji : j.val ≠ i := fun e => hj (Fin.ext e)
            apply LVec.extract_insertAt_of_disjoint
            rcases Nat.lt_or_gt_of_ne hji with hlt | hgt
            · left
              have := Nat.mul_le_mul_right W (show j.val + 1 ≤ i by omega)
              rw [Nat.add_mul, Nat.one_mul] at this; exact this
            · right
              have := Nat.mul_le_mul_right W (show i + 1 ≤ j.val by omega)
              rw [Nat.add_mul, Nat.one_mul] at this; simpa using this
        · exact h
  · simp only [hwe, Bool.false_eq_true, if_false]; exact h

#print axioms rfRead_width
#print axioms resizeU_of_width
#print axioms eval_index
#print axioms rfRead_eq
#print axioms rfWrite_abs

end LeanModels.Sv.FlatMem
