import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.Known2
import LeanModels.Sv.Lib.NatArith

/-!
# Register families: the one-driver rule and the packed view (`LeanModels.Sv`)

**Status: a `run2` library module** (provisional over `run2`; never trusted). The generic halves of a generate
family of registers at a symbolic size:

* `driversOk_of_ff`: an `always_ff`-only process list satisfies the one-driver rule (`driversOk`, `Hier2.lean`)
  when no process writes an input port and distinct processes write disjoint windows (for a row-major family:
  `pairwise_flatMap_range` and `DrvWin.overlaps_some_eq_false`, `Hier2Gen.lean`).
* **The packed view.** `packBV W n v`: `n` entries of `W` bits, entry `r` at bits `[r*W, r*W + W)` (row-major,
  little-endian, the layout of a flat `logic [n*W-1:0]`), the entries written in index order over zero
  (`bvInsertEntries`, over any old value; `bvInsertEntries_succ` peels the last entry). `getLsbD_bvInsertEntries`
  and `extractLsb'_packBV` read an entry,
  `packBV_eq_ofNat` is the packed vector as the sum `Σ_r (v r)·2^(r·W)`, `packBV_congr` says it reads only the
  entries below `n`.
* **The commit of a family over `LVec`.** `LVec.insertEntries W g n c` writes the windows `[r·W, r·W + W)`,
  `r = 0 … n-1`, in order over `c` (`LVec.insertEntries_succ` peels the last window, `LVec.width_insertEntries`,
  `@[simp]`, keeps the width); `LVec.insertEntries_ofBitVec`: writing every entry of a known family over any
  old value of the right width gives `ofBitVec (packBV …)` (the commit of a family that updates every window each
  cycle); `LVec.insertEntries_insertAt` and `LVec.foldl_range_insertAt_last` reorder the writes.
* **Unit writes**, for a family whose units are written one process at a time, some cycles not at all (a hold):
  `bvInsertAt_packBV` writes one unit of a `packBV`, `extract_ofBitVec_packBV` reads one, and
  `foldl_range_ofBitVec_packBV` folds such writes over the units `0 … m-1`.

Elsewhere: the arithmetic of row-major windows and their `Int` labels in `Lib/NatArith.lean` (the end of a row,
`rowMajor_le`, in `Hier2Gen.lean`), the commit restricted to one signal (`nbaFold`) in `NbaCommit.lean`, the known
bit `knownBit` and `LVec.shr_ofBitVec` in `Known2.lean`, a `flatMap` over the indices of a list
(`CombView.flatMap_range_eq`) in `CombViewArith.lean`, the clock step in `SeqProfile.lean`.
-/

namespace LeanModels.Sv

set_option autoImplicit false

open Lib (mul_add_mem_window_iff)

/-! ## The one-driver rule of an `always_ff` family -/

/-- **The one-driver rule of an `always_ff`-only family**: when every process is an `always_ff`, none writes an
input, and distinct processes write pairwise disjoint windows, `driversOk` holds. -/
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
def bvInsertEntries {m W : Nat} (v : Nat → BitVec W) (n : Nat) (x : BitVec m) : BitVec m :=
  (List.range n).foldl (fun acc r => bvInsertAt acc (r * W) (v r)) x

/-- `n` entries of `W` bits, entry `r` at bits `[r*W, r*W + W)` (row-major, little-endian). -/
def packBV (W n : Nat) (v : Nat → BitVec W) : BitVec (n * W) := bvInsertEntries v n 0#(n * W)

/-- Writing `n + 1` entries is writing `n`, then entry `n`. -/
theorem bvInsertEntries_succ {m W : Nat} (v : Nat → BitVec W) (n : Nat) (x : BitVec m) :
    bvInsertEntries v (n + 1) x = bvInsertAt (bvInsertEntries v n x) (n * W) (v n) := by
  simp [bvInsertEntries, List.range_succ, List.foldl_append]

/-- **Entry `r` of a written family** is `v r`, whatever the old value. -/
theorem getLsbD_bvInsertEntries {m W : Nat} (v : Nat → BitVec W) (x : BitVec m) :
    ∀ n, n * W ≤ m → ∀ r j, r < n → j < W → (bvInsertEntries v n x).getLsbD (r * W + j) = (v r).getLsbD j
  | 0, _, _, _, hr, _ => absurd hr (Nat.not_lt_zero _)
  | n + 1, hm, r, j, hr, hj => by
      have hnm : n * W + W ≤ m := by simpa [Nat.add_mul] using hm
      rw [bvInsertEntries_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · have h1 := rowMajor_le (K := W) hr
        rw [getLsbD_bvInsertAt _ _ _ (by omega), if_neg (by omega)]
        exact getLsbD_bvInsertEntries v x n (by omega) r j hr hj
      · rw [getLsbD_bvInsertAt _ _ _ (by omega), if_pos (by omega)]
        simp

/-- Reading entry `r` of `packBV`. -/
theorem extractLsb'_packBV {W n : Nat} (v : Nat → BitVec W) {r : Nat} (hr : r < n) :
    (packBV W n v).extractLsb' (r * W) W = v r := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
  exact getLsbD_bvInsertEntries v _ n (Nat.le_refl _) r j hr hj

/-- The sum `Σ_{r < n} (v r)·2^(r·W)` is below `2^(n·W)` and has the bits of the entries. -/
private theorem sum_lt_and_testBit {W : Nat} (v : Nat → BitVec W) : ∀ n,
    (List.range n).foldl (fun acc r => acc + (v r).toNat * 2 ^ (r * W)) 0 < 2 ^ (n * W) ∧
    ∀ r j, r < n → j < W → ((List.range n).foldl (fun acc r => acc + (v r).toNat * 2 ^ (r * W)) 0).testBit
      (r * W + j) = (v r).getLsbD j
  | 0 => ⟨by simp, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨hlt, hb⟩ := sum_lt_and_testBit v n
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (fun acc r => acc + (v r).toNat * 2 ^ (r * W)) 0 = S at hlt hb
    have hv := Nat.mul_le_mul_left (2 ^ (n * W)) (Nat.succ_le_of_lt (v n).isLt)
    rw [Nat.mul_succ] at hv
    rw [Nat.succ_mul, Nat.pow_add, Nat.mul_comm ((v n).toNat), Nat.add_comm S]
    refine ⟨by omega, fun r j hr hj => ?_⟩
    rw [Nat.testBit_two_pow_mul_add _ hlt]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
    · have := rowMajor_le (K := W) hr; rw [if_pos (by omega)]; exact hb r j hr hj
    · rw [if_neg (by omega), Nat.add_sub_cancel_left]; rfl

/-- **The packed vector is the sum of its entries**: `packBV W n v = Σ_{r < n} (v r)·2^(r·W)` at `n·W` bits. -/
theorem packBV_eq_ofNat (W n : Nat) (v : Nat → BitVec W) : packBV W n v =
    BitVec.ofNat (n * W) ((List.range n).foldl (fun acc r => acc + (v r).toNat * 2 ^ (r * W)) 0) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hW : 0 < W := Nat.pos_of_ne_zero fun h => by simp [h] at hi
  have hr : i / W < n := (Nat.div_lt_iff_lt_mul hW).mpr hi
  have hd : i / W * W + i % W = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i W
  have hp := getLsbD_bvInsertEntries v (0#(n * W)) n (Nat.le_refl _) _ _ hr (Nat.mod_lt i hW)
  have hs := (sum_lt_and_testBit v n).2 _ _ hr (Nat.mod_lt i hW)
  rw [hd] at hp hs
  rw [BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and, hs, packBV, hp]

/-- `packBV` reads only the entries below `n`. -/
theorem packBV_congr {W n : Nat} {u u' : Nat → BitVec W} (h : ∀ k, k < n → u k = u' k) :
    packBV W n u = packBV W n u' := by
  suffices ∀ m, m ≤ n → ∀ x : BitVec (n * W), bvInsertEntries u m x = bvInsertEntries u' m x from
    this n (Nat.le_refl _) _
  intro m; induction m with
  | zero => intro _ _; rfl
  | succ m ih => intro hm x; rw [bvInsertEntries_succ, bvInsertEntries_succ, ih (by omega), h m (by omega)]

/-! ## Unit writes into a packed family

A family whose units are written one process at a time, some cycles not at all (a hold). -/

/-- **Writing unit `m` of a packed family** updates that unit. -/
theorem bvInsertAt_packBV {W n m lo : Nat} (u : Nat → BitVec W) (a : BitVec W) (hm : m < n) (hlo : lo = m * W) :
    bvInsertAt (packBV W n u) lo a = packBV W n (fun k => if k = m then a else u k) := by
  subst hlo
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hW : 0 < W := Nat.pos_of_ne_zero fun h => by simp [h] at hi
  obtain ⟨r, j, hj, rfl⟩ : ∃ r j, j < W ∧ i = r * W + j :=
    ⟨i / W, i % W, Nat.mod_lt i hW, by rw [Nat.mul_comm]; exact (Nat.div_add_mod i W).symm⟩
  have hr : r < n := Nat.lt_of_not_le fun hc => by have := Nat.mul_le_mul_right W hc; omega
  rw [getLsbD_bvInsertAt _ _ _ hi]; simp only [mul_add_mem_window_iff hj]
  rw [packBV, packBV, getLsbD_bvInsertEntries _ _ n (Nat.le_refl _) _ _ hr hj,
    getLsbD_bvInsertEntries _ _ n (Nat.le_refl _) _ _ hr hj]
  by_cases h : r = m
  · subst h; simp
  · simp [h]

/-- Reading unit `r` of a known packed family. -/
theorem extract_ofBitVec_packBV {W n r lo : Nat} (v : Nat → BitVec W) (hr : r < n) (hlo : lo = r * W) :
    (LVec.ofBitVec (packBV W n v)).extract lo W = .ofBitVec (v r) := by
  subst hlo; rw [LVec.extract_ofBitVec _ (rowMajor_le hr), extractLsb'_packBV v hr]

/-- **A family of unit writes**: `ops k` writes `g k` into unit `k` (or nothing, when the unit already holds
`u k`), for `k = 0 … m-1`. -/
theorem foldl_range_ofBitVec_packBV {W N : Nat} (ops : Nat → LVec → LVec) (g u : Nat → BitVec W) : ∀ m,
    (∀ k u', k < m → u' k = u k → ops k (.ofBitVec (packBV W N u')) =
      .ofBitVec (packBV W N (fun i => if i = k then g k else u' i))) →
    (List.range m).foldl (fun acc k => ops k acc) (.ofBitVec (packBV W N u)) =
      .ofBitVec (packBV W N (fun i => if i < m then g i else u i))
  | 0, _ => by simp
  | m + 1, h => by
    rw [List.range_succ, List.foldl_append,
      foldl_range_ofBitVec_packBV ops g u m (fun k u' hk => h k u' (by omega)),
      List.foldl_cons, List.foldl_nil, h m _ (by omega) (by simp)]
    congr 2; funext i
    by_cases h1 : i = m
    · subst h1; simp
    · simp only [h1, if_false]; by_cases h2 : i < m <;> simp [h2] <;> omega

/-! ## The commit of a register family over `LVec` -/

namespace LVec

/-- Writing the windows `[r·W, r·W + W)`, `r = 0 … n-1`, in order: `g r` into window `r`, over `c`. -/
def insertEntries (W : Nat) (g : Nat → LVec) (n : Nat) (c : LVec) : LVec :=
  (List.range n).foldl (fun acc r => acc.insertAt (r * W) (g r)) c

/-- Writing `n + 1` windows is writing `n`, then window `n`. -/
theorem insertEntries_succ (W : Nat) (g : Nat → LVec) (n : Nat) (c : LVec) :
    insertEntries W g (n + 1) c = (insertEntries W g n c).insertAt (n * W) (g n) := by
  simp [insertEntries, List.range_succ, List.foldl_append]

/-- Writing windows keeps the width. -/
@[simp] theorem width_insertEntries (W : Nat) (g : Nat → LVec) (c : LVec) :
    ∀ n, (insertEntries W g n c).width = c.width
  | 0 => rfl
  | n + 1 => by rw [insertEntries_succ, width_insertAt, width_insertEntries W g c n]

private theorem getD_insertEntries_ofBitVec {W : Nat} (v : Nat → BitVec W) (c : LVec) : ∀ n, n * W ≤ c.width →
    ∀ r j, r < n → j < W → (insertEntries W (fun r => ofBitVec (v r)) n c).bits[r * W + j]?.getD .lx =
      Logic.ofBool ((v r).getLsbD j)
  | 0, _, _, _, hr, _ => absurd hr (Nat.not_lt_zero _)
  | n + 1, hm, r, j, hr, hj => by
    have hnm : n * W + W ≤ c.width := by simpa [Nat.add_mul] using hm
    simp only [insertEntries_succ, getD_insertAt, width_insertEntries, width_ofBitVec]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
    · have := rowMajor_le (K := W) hr
      rw [if_neg (by omega)]; exact getD_insertEntries_ofBitVec v c n (by omega) r j hr hj
    · rw [if_pos (by omega), if_pos (by omega), Nat.add_sub_cancel_left, getElem?_ofBitVec, if_pos hj]
      rfl

/-- **Writing every window of a known family over any old value of the right width gives the packed vector.** -/
theorem insertEntries_ofBitVec {W n : Nat} (v : Nat → BitVec W) (c : LVec) (hc : c.width = n * W) :
    insertEntries W (fun r => ofBitVec (v r)) n c = ofBitVec (packBV W n v) := by
  rw [eq_ofBitVec_iff]
  refine ⟨by rw [width_insertEntries, hc], fun i hi => ?_⟩
  have hW : 0 < W := Nat.pos_of_ne_zero fun h => by simp [h] at hi
  have hr : i / W < n := (Nat.div_lt_iff_lt_mul hW).mpr hi
  have hd : i / W * W + i % W = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i W
  have hlt : i < (insertEntries W (fun r => ofBitVec (v r)) n c).bits.size := by
    show i < LVec.width _; rw [width_insertEntries, hc]; exact hi
  have hb := getD_insertEntries_ofBitVec v c n (by omega) (i / W) (i % W) hr (Nat.mod_lt i hW)
  rw [hd, Array.getElem?_eq_getElem hlt, Option.getD_some] at hb
  have hp := getLsbD_bvInsertEntries v (0#(n * W)) n (Nat.le_refl _) (i / W) (i % W) hr (Nat.mod_lt i hW)
  rw [hd] at hp
  rw [Array.getElem?_eq_getElem hlt, hb, packBV, hp]

/-- A write of a window above the first `n` (of entries of width `W`) commutes with `insertEntries`. -/
theorem insertEntries_insertAt {W : Nat} (g : Nat → LVec) (hg : ∀ k, (g k).width = W) (a x : LVec) (m : Nat) :
    ∀ n, n ≤ m → insertEntries W g n (x.insertAt (m * W) a) = (insertEntries W g n x).insertAt (m * W) a
  | 0, _ => rfl
  | n + 1, h => by
    have := Nat.mul_le_mul_right W h; rw [Nat.succ_mul] at this
    rw [insertEntries_succ, insertEntries_succ, insertEntries_insertAt g hg a x m n (by omega),
      insertAt_comm (.inr (by rw [hg]; omega))]

/-- Writing a constant `g` into the last window first, then into the others in order, is `insertEntries`. -/
theorem foldl_range_insertAt_last {W N : Nat} (hN : 1 ≤ N) (g c : LVec) (hg : g.width = W) :
    (List.range (N - 1)).foldl (fun acc k => acc.insertAt (k * W) g) (c.insertAt ((N - 1) * W) g) =
      insertEntries W (fun _ => g) N c := by
  have := insertEntries_insertAt (W := W) (fun _ => g) (fun _ => hg) g c (N - 1) (N - 1) (Nat.le_refl _)
  rw [show N = N - 1 + 1 by omega, insertEntries_succ, ← this]; rfl

end LVec

#print axioms driversOk_of_ff
#print axioms getLsbD_bvInsertEntries
#print axioms extractLsb'_packBV
#print axioms packBV_eq_ofNat
#print axioms bvInsertAt_packBV
#print axioms foldl_range_ofBitVec_packBV
#print axioms LVec.insertEntries_ofBitVec
#print axioms LVec.foldl_range_insertAt_last

end LeanModels.Sv
