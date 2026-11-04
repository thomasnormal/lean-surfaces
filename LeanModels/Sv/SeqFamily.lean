import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.Known2

/-!
# Register families: the one-driver rule and the packed view (`LeanModels.Sv`, S1 core)

**Status: a `run2` library module** (provisional over `run2`; never trusted). Imported by no existing
module. The generic halves of a generate family of registers at a symbolic size:

* `driversOk_of_ff`: an `always_ff`-only process list satisfies the one-driver rule (`driversOk`,
  `Hier2.lean`) when no process writes an input port and distinct processes write disjoint windows
  (for a row-major family: `pairwise_flatMap_range` and `DrvWin.overlaps_some_eq_false`, Hier2Gen).
* `packBV W n v`: `n` entries of `W` bits, entry `r` at bits `[r*W, r*W + W)` (row-major,
  little-endian, the layout of a flat `logic [n*W-1:0]`). `extractLsb'_packBV` reads an entry;
  `insertAll_eq_packBV` says writing every entry, in index order, over any old value, gives `packBV`:
  the commit of a family that updates every window each cycle.
-/

namespace LeanModels.Sv

set_option autoImplicit false

/-! ## The one-driver rule of an `always_ff` family -/

theorem driversOk_of_ff {names inputs : List String} {ps : List Process2}
    (hff : ∀ p ∈ ps, ∃ c b, p = .alwaysFF c b)
    (hin : ∀ n ∈ ps.flatMap Process2.procWrites, inputs.contains n = false)
    (hdisj : ps.Pairwise fun p q => ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false) :
    driversOk names inputs ps = true := by
  have hdw : driverWins names ps = [] := by
    simp only [driverWins, List.flatMap_eq_nil_iff]
    intro p hp
    obtain ⟨c, b, rfl⟩ := hff p hp
    rfl
  rw [driversOk_iff, hdw]
  refine ⟨List.Pairwise.nil, fun w hw => absurd hw List.not_mem_nil, hin, hdisj.imp fun {p q} h => ?_⟩
  have hany : ((p.procWinsOn names).any fun a => (q.procWinsOn names).any fun b => a.overlaps b) =
      false := by
    rw [List.any_eq_false]
    intro a ha
    rw [Bool.not_eq_true, List.any_eq_false]
    intro b hb
    rw [h a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1]
    exact Bool.false_ne_true
  simp [Process2.exclClash, hany]

/-! ## The packed view of a register family -/

/-- Write `v r` at `[r*W, r*W + W)` for `r = 0, …, n-1`, in that order, over `x`. -/
def insFold {m W : Nat} (v : Nat → BitVec W) (n : Nat) (x : BitVec m) : BitVec m :=
  (List.range n).foldl (fun acc r => bvInsertAt acc (r * W) (v r)) x

/-- `n` entries of `W` bits, entry `r` at bits `[r*W, r*W + W)` (row-major, little-endian). -/
def packBV (W n : Nat) (v : Nat → BitVec W) : BitVec (n * W) := insFold v n 0#(n * W)

theorem insFold_succ {m W : Nat} (v : Nat → BitVec W) (n : Nat) (x : BitVec m) :
    insFold v (n + 1) x = bvInsertAt (insFold v n x) (n * W) (v n) := by
  simp [insFold, List.range_succ, List.foldl_append]

theorem mul_add_le {r n W : Nat} (h : r < n) : r * W + W ≤ n * W := by
  have := Nat.mul_le_mul_right W (show r + 1 ≤ n by omega)
  simpa [Nat.add_mul] using this

/-- **Entry `r` of a written family** is `v r`, whatever the old value. -/
theorem getLsbD_insFold {m W : Nat} (v : Nat → BitVec W) (x : BitVec m) :
    ∀ n, n * W ≤ m → ∀ r j, r < n → j < W → (insFold v n x).getLsbD (r * W + j) = (v r).getLsbD j
  | 0, _, _, _, hr, _ => absurd hr (Nat.not_lt_zero _)
  | n + 1, hm, r, j, hr, hj => by
      have hnm : n * W + W ≤ m := by simpa [Nat.add_mul] using hm
      rw [insFold_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · have h1 := mul_add_le (W := W) hr
        rw [getLsbD_bvInsertAt _ _ _ (by omega), if_neg (by omega)]
        exact getLsbD_insFold v x n (by omega) r j hr hj
      · rw [getLsbD_bvInsertAt _ _ _ (by omega), if_pos (by omega)]
        simp

/-- Reading entry `r` of `packBV`. -/
theorem extractLsb'_packBV {W n : Nat} (v : Nat → BitVec W) {r : Nat} (hr : r < n) :
    (packBV W n v).extractLsb' (r * W) W = v r := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
  exact getLsbD_insFold v _ n (Nat.le_refl _) r j hr hj

/-- **Writing every entry over any old value gives `packBV`.** -/
theorem insFold_eq_packBV {W n : Nat} (v : Nat → BitVec W) (x : BitVec (n * W)) :
    insFold v n x = packBV W n v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hW : 0 < W := Nat.pos_of_ne_zero fun h => by simp [h] at hi
  have hd := Nat.div_add_mod i W
  have hr : i / W < n := by
    rcases Nat.lt_or_ge (i / W) n with h | h
    · exact h
    · have := Nat.mul_le_mul_right W h
      have := Nat.mod_lt i hW
      rw [Nat.mul_comm] at hd
      omega
  rw [← hd, Nat.mul_comm W (i / W), getLsbD_insFold v x n (Nat.le_refl _) _ _ hr (Nat.mod_lt i hW),
    packBV, getLsbD_insFold v _ n (Nat.le_refl _) _ _ hr (Nat.mod_lt i hW)]

#print axioms driversOk_of_ff
#print axioms getLsbD_insFold
#print axioms extractLsb'_packBV
#print axioms insFold_eq_packBV

end LeanModels.Sv
