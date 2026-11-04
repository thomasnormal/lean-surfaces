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
* Shared lemmas of the register-family proofs (moved from the matmul G1 reference): the label
  facts of row-major windows (`win_*`, `n_bound`), `overlaps_comm`, `flatMap_range_eq`, the known
  bit `bit`, the commit of a family over `LVec` (`insertAt_full`, `lfold_ofBitVec`, `width_foldl`,
  `sum_packed`), and datapath arithmetic (`shr_ofBitVec`, `sx_eq`, `mac`, `sh_step`, `keq`).
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

/-! ## Shared lemmas of the register-family proofs

Design-independent, moved verbatim from the matmul G1 reference (`svgolf/tasks/matmul/reference/
matmul_g1.lean`, PLAN4 Gate 3) so the sorter and later references reuse them. The two about the
clock step itself (`ffDisjB_of_pairwise`, `flatMap_ffUpd`) are in `SeqProfile.lean`, after the
definitions they name. `cond_bit` carries no `simp` attribute here; a proof adds it locally. -/

/-! ### Instantiation arithmetic: the label facts of a row-major family's windows -/

theorem cast3 (a b c : Nat) : ((a * b * c : Nat) : Int) = (a : Int) * b * c := by simp

theorem except_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

theorem natAbs_pred {x : Nat} (h : 0 < x) : ((x : Int) - 1).natAbs + 1 = x := by omega

/-- Entry `(i, j)` of an `N×N` array of `w`-bit entries lies inside it. -/
theorem win_le {N w i j : Nat} (hi : i < N) (hj : j < N) : (i * N + j) * w + w ≤ N * N * w := by
  have h : i * N + j + 1 ≤ N * N := by
    have := Nat.mul_le_mul_right N (show i + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have := Nat.mul_le_mul_right w h; rwa [Nat.add_mul, Nat.one_mul] at this

/-- The label facts of an in-range window `[x, x + w)` of a `y`-bit vector, from `Nat` ones. -/
theorem win_facts (x y : Int) {lo w c : Nat} (h : lo + w ≤ c) (hw : 0 < w) (hx : (lo : Int) = x)
    (hy : (c : Int) = y) : 0 ≤ x ∧ x.toNat = lo ∧ x + w - 1 < y ∧ 1 ≤ x + w ∧ (x + w).toNat = lo + w :=
  ⟨by omega, by omega, by omega, by omega, by omega⟩
theorem win_min (a : Int) {w : Int} (h : 0 < w) : min (a + w - 1) a = a := by omega
theorem win_max (a : Int) {w : Int} (h : 0 < w) : max (a + w - 1) a = a + w - 1 := by omega
theorem win_wid (a w : Int) : a + w - 1 - a + 1 = w := by omega

theorem n_bound {env : IEnv} {N : Nat} (h : env.vals.lookup "N" = some (N : Int)) (g : String)
    (hg : g ≠ "N") (i : Int) : evalInt (env.bindVal g i) (.paramRef "N" none) = .ok (N : Int) ∧
      (PExpr.paramRef "N" none).isInt (env.bindVal g i) = true := by
  have h' : (env.bindVal g i).vals.lookup "N" = some (N : Int) := by
    simp [IEnv.bindVal, List.lookup, h, beq_false_of_ne (Ne.symm hg)]
  exact ⟨evalInt_paramRef_of h', isInt_paramRef_of h'⟩

/-! ### Driver windows and lists -/

theorem overlaps_comm (a b : DrvWin) : a.overlaps b = b.overlaps a := by
  obtain ⟨n, _ | ⟨l, w⟩⟩ := a <;> obtain ⟨n', _ | ⟨l', w'⟩⟩ := b <;> simp only [DrvWin.overlaps] <;>
    rw [Bool.beq_comm (a := n)] <;> simp only [Bool.and_comm]

theorem flatMap_range_eq {α β : Type} (g : α → List β) : ∀ (l : List α) (F : Nat → List β),
    (∀ i (h : i < l.length), F i = g l[i]) → (List.range l.length).flatMap F = l.flatMap g
  | [], _, _ => rfl
  | a :: l, F, h => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.flatMap_cons,
      h 0 (by simp), flatMap_range_eq g l _ fun i hi => h (i + 1) (by simp; omega)]
    rfl

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-! ### Known bits and the commit of a register family -/

/-- The known 1-bit value `b`. -/
abbrev bit (b : Bool) : LVec := LVec.ofBitVec (BitVec.ofBool b)

theorem cond_bit (b : Bool) : (bit b).condTrue = b := by cases b <;> simp [LVec.condTrue_ofBitVec]

theorem l0_bit : (⟨#[.l0]⟩ : LVec).resizeU 1 = bit false := by decide
theorem l1_bit : (⟨#[.l1]⟩ : LVec).resizeU 1 = bit true := by decide

theorem commit_nil (st : SvState) : commitNba2 st [] = st := rfl

theorem insertAt_full (v p : LVec) (h : p.width = v.width) : v.insertAt 0 p = p := by
  apply LVec.ext_getElem?; intro i
  simp only [LVec.insertAt, Array.getElem?_ofFn, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero, h]
  by_cases hi : i < v.width
  · simp only [hi, dite_true, if_true]
    rw [Array.getElem?_eq_getElem (by unfold LVec.width at h hi; omega)]; rfl
  · simp only [hi, dite_false]
    exact (Array.getElem?_eq_none (by unfold LVec.width at h hi; omega)).symm

theorem width_foldl (q : NbaQueue2) (c : LVec) :
    (q.foldl (fun acc u => acc.insertAt u.2.1 u.2.2) c).width = c.width := by
  induction q generalizing c with
  | nil => rfl
  | cons u q ih => rw [List.foldl_cons, ih, LVec.width_insertAt]

/-- Writing windows `[r·W, r·W + W)`, `r = 0 … n-1`, in order. -/
def lfold (W : Nat) (g : Nat → LVec) (n : Nat) (c : LVec) : LVec :=
  (List.range n).foldl (fun acc r => acc.insertAt (r * W) (g r)) c

theorem lfold_succ (W : Nat) (g : Nat → LVec) (n : Nat) (c : LVec) :
    lfold W g (n + 1) c = (lfold W g n c).insertAt (n * W) (g n) := by
  simp [lfold, List.range_succ, List.foldl_append]

theorem width_lfold (W : Nat) (g : Nat → LVec) (c : LVec) : ∀ n, (lfold W g n c).width = c.width
  | 0 => rfl
  | n + 1 => by rw [lfold_succ, LVec.width_insertAt, width_lfold W g c n]

theorem lfold_bits {W : Nat} (v : Nat → BitVec W) (c : LVec) : ∀ n, n * W ≤ c.width → ∀ r j, r < n →
    j < W → (lfold W (fun r => LVec.ofBitVec (v r)) n c).bits[r * W + j]?.getD .lx =
      Logic.ofBool ((v r).getLsbD j)
  | 0, _, _, _, hr, _ => absurd hr (Nat.not_lt_zero _)
  | n + 1, hm, r, j, hr, hj => by
    have hnm : n * W + W ≤ c.width := by simpa [Nat.add_mul] using hm
    simp only [lfold_succ, LVec.getD_insertAt, width_lfold, LVec.width_ofBitVec]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
    · have := mul_add_le (W := W) hr
      rw [if_neg (by omega)]; exact lfold_bits v c n (by omega) r j hr hj
    · rw [if_pos (by omega), if_pos (by omega), Nat.add_sub_cancel_left, LVec.getElem?_ofBitVec, if_pos hj]
      rfl

/-- **Writing every window over any old value of the right width gives the packed vector.** -/
theorem lfold_ofBitVec {W n : Nat} (v : Nat → BitVec W) (c : LVec) (hc : c.width = n * W) :
    lfold W (fun r => LVec.ofBitVec (v r)) n c = LVec.ofBitVec (packBV W n v) := by
  rw [LVec.eq_ofBitVec_iff]
  refine ⟨by rw [width_lfold, hc], fun i hi => ?_⟩
  have hW : 0 < W := Nat.pos_of_ne_zero fun h => by simp [h] at hi
  have hr : i / W < n := (Nat.div_lt_iff_lt_mul hW).mpr hi
  have hd : i / W * W + i % W = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i W
  have hlt : i < (lfold W (fun r => LVec.ofBitVec (v r)) n c).bits.size := by
    show i < LVec.width _; rw [width_lfold, hc]; exact hi
  have hb := lfold_bits v c n (by omega) (i / W) (i % W) hr (Nat.mod_lt i hW)
  rw [hd, Array.getElem?_eq_getElem hlt, Option.getD_some] at hb
  have hp := getLsbD_insFold v (0#(n * W)) n (Nat.le_refl _) (i / W) (i % W) hr (Nat.mod_lt i hW)
  rw [hd] at hp
  rw [Array.getElem?_eq_getElem hlt, hb, packBV, hp]

theorem sum_packed {W : Nat} (v : Nat → BitVec W) : ∀ n,
    (List.range n).foldl (fun acc r => acc + (v r).toNat * 2 ^ (r * W)) 0 < 2 ^ (n * W) ∧
    ∀ r j, r < n → j < W → ((List.range n).foldl (fun acc r => acc + (v r).toNat * 2 ^ (r * W)) 0).testBit
      (r * W + j) = (v r).getLsbD j
  | 0 => ⟨by simp, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨hlt, hb⟩ := sum_packed v n
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (fun acc r => acc + (v r).toNat * 2 ^ (r * W)) 0 = S at hlt hb
    have hv := Nat.mul_le_mul_left (2 ^ (n * W)) (Nat.succ_le_of_lt (v n).isLt)
    rw [Nat.mul_succ] at hv
    rw [Nat.succ_mul, Nat.pow_add, Nat.mul_comm ((v n).toNat), Nat.add_comm S]
    refine ⟨by omega, fun r j hr hj => ?_⟩
    rw [Nat.testBit_two_pow_mul_add _ hlt]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
    · have := mul_add_le (W := W) hr; rw [if_pos (by omega)]; exact hb r j hr hj
    · rw [if_neg (by omega), Nat.add_sub_cancel_left]; rfl

/-! ### Bit-vector arithmetic of datapaths: shifts, sign extension, multiply-accumulate, counters -/

theorem shr_ofBitVec {w v : Nat} (x : BitVec w) (y : BitVec v) :
    (LVec.ofBitVec x).shr (LVec.ofBitVec y) = LVec.ofBitVec (x >>> y.toNat) := by
  rw [LVec.eq_ofBitVec_iff]
  refine ⟨by simp [LVec.shr, LVec.shiftAmount?, LVec.width]; exact LVec.width_ofBitVec x, fun i hi => ?_⟩
  simp only [LVec.shr, LVec.shiftAmount?, LVec.toNat?_ofBitVec, Array.getElem?_ofFn, LVec.width_ofBitVec,
    hi, dite_true, BitVec.getLsbD_ushiftRight, LVec.getElem?_ofBitVec]
  by_cases h : i + y.toNat < w
  · simp [h, Nat.add_comm]
  · simp only [h, Nat.add_comm, ↓reduceIte, Option.getD_none]
    rw [BitVec.getLsbD_of_ge x _ (by omega)]; rfl

/-- `{{AccW{y[lo+W-1]}}, y[lo +: W]}` is the sign extension of the entry. -/
theorem sx_eq {n p lo W : Nat} (hW : 1 ≤ W) (y : BitVec n) (AccW : Nat) (hp : p = lo + W - 1) :
    LVec.ofBitVec ((y.extractLsb' p 1).replicate AccW ++ y.extractLsb' lo W) =
      LVec.ofBitVec ((y.extractLsb' lo W).signExtend (AccW + W)) := by
  rw [LVec.eq_ofBitVec_iff]
  refine ⟨by simp [Nat.add_comm], fun i hi => ?_⟩
  rw [LVec.getElem?_ofBitVec, if_pos (by omega)]
  congr 2
  rw [BitVec.getLsbD_append, BitVec.getLsbD_signExtend]
  by_cases h : i < W
  · rw [if_pos h, if_pos h, decide_eq_true (by omega : i < AccW + W), Bool.true_and]
  · rw [if_neg h, if_neg h, BitVec.getLsbD_replicate, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_extractLsb', Nat.mod_one, hp, show lo + W - 1 + 0 = lo + (W - 1) by omega]
    simp only [show i - W < 1 * AccW by omega, show W - 1 < W by omega, show i < AccW + W by omega,
      show (0 : Nat) < 1 by omega, decide_true, Bool.true_and]

theorem setWidth_sext {W : Nat} (y : BitVec W) (m : Nat) : (y.signExtend (m + W)).setWidth m = y.signExtend m := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.getLsbD_signExtend, decide_eq_true hi,
    decide_eq_true (by omega : i < m + W), Bool.true_and, Bool.true_and]

/-- **One multiply-accumulate, mod `2^AccW`.** -/
theorem mac {AccW W : Nat} (x : BitVec AccW) (ya yb : BitVec W) :
    (x.setWidth (AccW + W) + ya.signExtend (AccW + W) * yb.signExtend (AccW + W)).setWidth AccW =
      x + BitVec.ofInt AccW (ya.toInt * yb.toInt) := by
  rw [BitVec.setWidth_add _ _ (by omega), BitVec.setWidth_mul _ _ (by omega),
    BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, setWidth_sext, setWidth_sext,
    BitVec.ofInt_mul]; rfl

theorem ext_shr {n : Nat} (A : BitVec n) (s lo W : Nat) : (A >>> s).extractLsb' lo W = A.extractLsb' (s + lo) W := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [BitVec.getLsbD_ushiftRight, Nat.add_assoc]

theorem c32_nat (v : Nat) : LVec.ofInt 32 (v : Int) = LVec.ofBitVec (BitVec.ofNat 32 v) := by
  rw [LVec.ofInt, LVec.ofNat_eq_ofBitVec, LVec.ofBitVec_inj]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  show ((v : Int) % 2 ^ 32).toNat % 2 ^ 32 = v % 2 ^ 32
  simp only [Nat.reducePow, Int.reducePow]; omega

theorem kinc (t : Nat) : BitVec.ofNat 32 t + 1#32 = BitVec.ofNat 32 (t + 1) := by
  apply BitVec.eq_of_toNat_eq; simp <;> omega

theorem sh_step {n : Nat} (X : BitVec n) (s d : Nat) (y : BitVec 32) (hy : y.toNat = d) :
    ((LVec.ofBitVec (X >>> s)).shr (LVec.ofBitVec y)).resizeU n = LVec.ofBitVec (X >>> (s + d)) := by
  rw [shr_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, LVec.ofBitVec_inj, hy]
  apply BitVec.eq_of_getLsbD_eq; intro i _; simp [BitVec.getLsbD_ushiftRight, Nat.add_assoc]

theorem keq {t N : Nat} (ht : t < N) (hN : N < 2 ^ 32) :
    BitVec.ofNat 32 t = BitVec.ofNat 32 N - 1#32 ↔ t + 1 = N := by
  rw [← BitVec.toNat_inj, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at hN ⊢; omega

/-! ## Unit writes into a packed family, and per-signal commits (from the sorter reference)

Design-independent, from `svgolf/tasks/sorter/reference/sorter_ins.lean` (PLAN4 Gate 5): a family
whose units are written one process at a time, some cycles not at all (a hold). `packBV_upd` writes
one unit of a `packBV`; `packBV_family` folds such writes over the units `0 … m-1` (a hold writes
nothing when the unit already holds its value); `nbaFold n q x` is the commit of a queue `q`
restricted to the signal `n`, so a state of separate registers commits register by register. -/

/-- Bit `r·W + j` (`j < W`) lies in window `[m·W, m·W + W)` exactly when `r = m`. -/
theorem unit_win_iff {W r m j : Nat} (hj : j < W) : (m * W ≤ r * W + j ∧ r * W + j < m * W + W) ↔ r = m := by
  refine ⟨fun ⟨h1, h2⟩ => ?_, by rintro rfl; omega⟩
  rcases Nat.lt_trichotomy r m with h | h | h
  · have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt h); rw [Nat.succ_mul] at this; omega
  · exact h
  · have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt h); rw [Nat.succ_mul] at this; omega

/-- `packBV` reads only the units below `n`. -/
theorem packBV_congr {W n : Nat} {u u' : Nat → BitVec W} (h : ∀ k, k < n → u k = u' k) :
    packBV W n u = packBV W n u' := by
  suffices ∀ m, m ≤ n → ∀ x : BitVec (n * W), insFold u m x = insFold u' m x from this n (Nat.le_refl _) _
  intro m; induction m with
  | zero => intro _ _; rfl
  | succ m ih => intro hm x; rw [insFold_succ, insFold_succ, ih (by omega), h m (by omega)]

/-- **Writing unit `m` of a packed family** updates that unit. -/
theorem packBV_upd {W n m lo : Nat} (u : Nat → BitVec W) (a : BitVec W) (hm : m < n) (hlo : lo = m * W) :
    bvInsertAt (packBV W n u) lo a = packBV W n (fun k => if k = m then a else u k) := by
  subst hlo
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hW : 0 < W := Nat.pos_of_ne_zero fun h => by simp [h] at hi
  obtain ⟨r, j, hj, rfl⟩ : ∃ r j, j < W ∧ i = r * W + j :=
    ⟨i / W, i % W, Nat.mod_lt i hW, by rw [Nat.mul_comm]; exact (Nat.div_add_mod i W).symm⟩
  have hr : r < n := Nat.lt_of_not_le fun hc => by have := Nat.mul_le_mul_right W hc; omega
  rw [getLsbD_bvInsertAt _ _ _ hi]; simp only [unit_win_iff hj]
  rw [packBV, packBV, getLsbD_insFold _ _ n (Nat.le_refl _) _ _ hr hj, getLsbD_insFold _ _ n (Nat.le_refl _) _ _ hr hj]
  by_cases h : r = m
  · subst h; simp
  · simp [h]

/-- Reading unit `r` of a known packed family. -/
theorem extract_packBV {W n r lo : Nat} (v : Nat → BitVec W) (hr : r < n) (hlo : lo = r * W) :
    (LVec.ofBitVec (packBV W n v)).extract lo W = .ofBitVec (v r) := by
  subst hlo; rw [LVec.extract_ofBitVec _ (mul_add_le hr), extractLsb'_packBV v hr]

/-- **A family of unit writes**: `ops k` writes `g k` into unit `k` (or nothing, when the unit
already holds `u k`), for `k = 0 … m-1`. -/
theorem packBV_family {W N : Nat} (ops : Nat → LVec → LVec) (g u : Nat → BitVec W) : ∀ m, m ≤ N →
    (∀ k u', k < m → u' k = u k → ops k (.ofBitVec (packBV W N u')) =
      .ofBitVec (packBV W N (fun i => if i = k then g k else u' i))) →
    (List.range m).foldl (fun acc k => ops k acc) (.ofBitVec (packBV W N u)) =
      .ofBitVec (packBV W N (fun i => if i < m then g i else u i))
  | 0, _, _ => by simp
  | m + 1, hm, h => by
    rw [List.range_succ, List.foldl_append, packBV_family ops g u m (by omega) (fun k u' hk => h k u' (by omega)),
      List.foldl_cons, List.foldl_nil, h m _ (by omega) (by simp)]
    congr 2; funext i
    by_cases h1 : i = m
    · subst h1; simp
    · simp only [h1, if_false]; by_cases h2 : i < m <;> simp [h2] <;> omega

/-- A write of a window above the first `n` units commutes with `lfold`. -/
theorem lfold_insertAt {W : Nat} (g : Nat → LVec) (hg : ∀ k, (g k).width = W) (a x : LVec) (m : Nat) :
    ∀ n, n ≤ m → lfold W g n (x.insertAt (m * W) a) = (lfold W g n x).insertAt (m * W) a
  | 0, _ => rfl
  | n + 1, h => by
    have := Nat.mul_le_mul_right W h; rw [Nat.succ_mul] at this
    rw [lfold_succ, lfold_succ, lfold_insertAt g hg a x m n (by omega),
      LVec.insertAt_comm (.inr (by rw [hg]; omega))]

/-- The last unit written first, then the others in order: `lfold` of a constant. -/
theorem lfold_last {W N : Nat} (hN : 1 ≤ N) (g c : LVec) (hg : g.width = W) :
    (List.range (N - 1)).foldl (fun acc k => acc.insertAt (k * W) g) (c.insertAt ((N - 1) * W) g) =
      lfold W (fun _ => g) N c := by
  have := lfold_insertAt (W := W) (fun _ => g) (fun _ => hg) g c (N - 1) (N - 1) (Nat.le_refl _)
  rw [show N = N - 1 + 1 by omega, lfold_succ, ← this]; rfl

/-- The writes of a queue to the signal `n`, in order, over `x`. -/
def nbaFold (n : String) (q : NbaQueue2) (x : LVec) : LVec :=
  q.foldl (fun acc u => if u.1 = n then acc.insertAt u.2.1 u.2.2 else acc) x

theorem nbaFold_append (n : String) (a b : NbaQueue2) (x : LVec) :
    nbaFold n (a ++ b) x = nbaFold n b (nbaFold n a x) :=
  List.foldl_append ..

theorem nbaFold_flatMap (n : String) (f : Nat → NbaQueue2) : ∀ (l : List Nat) (x : LVec),
    nbaFold n (l.flatMap f) x = l.foldl (fun acc k => nbaFold n (f k) acc) x
  | [], _ => rfl
  | a :: l, x => by rw [List.flatMap_cons, nbaFold_append, nbaFold_flatMap n f l]; rfl

theorem nbaFold_flatMap_id {n : String} {f : Nat → NbaQueue2} (h : ∀ k x, nbaFold n (f k) x = x) :
    ∀ (l : List Nat) (x : LVec), nbaFold n (l.flatMap f) x = x
  | [], _ => rfl
  | a :: l, x => by rw [List.flatMap_cons, nbaFold_append, h, nbaFold_flatMap_id h l]

theorem width_nbaFold (n : String) : ∀ (q : NbaQueue2) (x : LVec), (nbaFold n q x).width = x.width
  | [], _ => rfl
  | u :: q, x => by
    simp only [nbaFold, List.foldl_cons]
    rw [← nbaFold, width_nbaFold n q]; split <;> simp

#print axioms driversOk_of_ff
#print axioms getLsbD_insFold
#print axioms extractLsb'_packBV
#print axioms insFold_eq_packBV
#print axioms lfold_ofBitVec
#print axioms sum_packed
#print axioms sx_eq
#print axioms mac
#print axioms packBV_upd
#print axioms packBV_family
#print axioms lfold_last

end LeanModels.Sv
