import LeanModels.Sv.CombKnownBits

/-!
# `CombWord`: the glue from the bit equations of a word-level operator to `BitVec` arithmetic (WP-B2)

`sv_equations` states the Boolean value of an `assign` whose right-hand side uses `+` or `-` in the faithful
nested form of the SystemVerilog, over the bit functions of `CombKnownBits.lean`:

```
st.boolAt "t" k = XF.addBits (N + 1) (XF.addBits (N + 1) (XF.zext N (st.boolAt "a")) (N + 1)
                    (XF.zext N (st.boolAt "b"))) (N + 1) (XF.zext 1 (st.boolAt "cin")) k
```

`XF.zext n f` is the zero extension of an `n`-bit bit function (what the `Resize` marker that slang puts around a
narrower operand computes, `Expr2.xfBits`). This file is the plain-Lean half the player's proof uses: from such an
equation (`∀ k < w, g k = XF.addBits w f w f' k`) to `BitVec` addition, subtraction and multiplication at the width `w`
(`XF.bv_addBits`, `XF.bv_subBits`, `XF.bv_mulBits`; `XF.val_mulBits` is the value of a product in `Nat`), and `XF.bv_zext`
for the markers. Everything is for a symbolic width.
-/

namespace LeanModels.Sv
namespace XF

/-- Zero extension of a bit function from `n` bits (what `Expr2.xfBits (.resize ..)` computes). -/
def zext (n : Nat) (f : Nat → Bool) : Nat → Bool := fun j => decide (j < n) && f j

/-- Bit functions that agree below `n` have the same value of the first `n` bits. -/
theorem val_congr_lt {f g : Nat → Bool} :
    ∀ {n : Nat}, (∀ j, j < n → f j = g j) → val f n = val g n
  | 0, _ => rfl
  | n + 1, h => by
      simp only [val]
      rw [val_congr_lt (fun j hj => h j (by omega)), h n (by omega)]

theorem val_zext (n : Nat) (f : Nat → Bool) : ∀ m, n ≤ m → val (zext n f) m = val f n
  | 0, h => by
      obtain rfl : n = 0 := by omega
      rfl
  | m + 1, h => by
      by_cases hn : n ≤ m
      · simp only [val]
        rw [val_zext n f m hn]
        have : zext n f m = false := by simp [zext]; omega
        simp [this]
      · obtain rfl : n = m + 1 := by omega
        simp only [val]
        rw [val_congr_lt (f := zext (m + 1) f) (g := f) (fun j hj => by simp [zext]; omega)]
        simp [zext]

theorem val_testBit (x : Nat) : ∀ n, val x.testBit n = x % 2 ^ n
  | 0 => by simp [val, Nat.mod_one]
  | n + 1 => by
      simp only [val, val_testBit x n]
      rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
      have h2 : x / 2 ^ n % 2 = 0 ∨ x / 2 ^ n % 2 = 1 := by omega
      rcases h2 with h | h <;> simp [h]

theorem toNat_bv (w : Nat) (f : Nat → Bool) : (bv w f).toNat = val f w := by
  unfold bv
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (val_lt f w)]

theorem bv_congr_lt {w : Nat} {f g : Nat → Bool} (h : ∀ k, k < w → f k = g k) : bv w f = bv w g := by
  unfold bv; rw [val_congr_lt h]

/-- A zero-extended bit function is the `setWidth` of the narrow vector. -/
theorem bv_zext {n m : Nat} (f : Nat → Bool) (h : n ≤ m) :
    bv m (zext n f) = (bv n f).setWidth m := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_bv, val_zext n f m h, BitVec.toNat_setWidth, toNat_bv, Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le (val_lt f n) (Nat.pow_le_pow_right (by omega) h)

/-- **Addition glue.** The bit equations of a sum are `BitVec` addition. -/
theorem bv_addBits {w : Nat} {g f f' : Nat → Bool} (h : ∀ k, k < w → g k = addBits w f w f' k) :
    bv w g = bv w f + bv w f' := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_bv, val_congr_lt (g := (val f w + val f' w).testBit) h, val_testBit, BitVec.toNat_add,
    toNat_bv, toNat_bv]

/-- **Subtraction glue.** -/
theorem bv_subBits {w : Nat} {g f f' : Nat → Bool} (h : ∀ k, k < w → g k = subBits w f w f' k) :
    bv w g = bv w f - bv w f' := by
  apply BitVec.eq_of_toNat_eq
  have e : subBits w f w f' = (val f w + (2 ^ w - val f' w)).testBit := by
    funext k; simp [subBits]
  rw [toNat_bv, val_congr_lt (g := (val f w + (2 ^ w - val f' w)).testBit)
      (fun k hk => by rw [h k hk, e]), val_testBit, BitVec.toNat_sub, toNat_bv, toNat_bv]
  congr 1
  omega

/-- **Multiplication glue** (WP-B2): the bit equations of a product are `BitVec` multiplication, modulo `2^w`. -/
theorem bv_mulBits {w : Nat} {g f f' : Nat → Bool} (h : ∀ k, k < w → g k = mulBits w f w f' k) :
    bv w g = bv w f * bv w f' := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_bv, val_congr_lt (g := (val f w * val f' w).testBit) h, val_testBit, BitVec.toNat_mul,
    toNat_bv, toNat_bv]

/-- **The value of a product**, in `Nat`: the first `w` bits of `mulBits` are the product of the operands' values
modulo `2^w`. -/
theorem val_mulBits (wa wb w : Nat) (fa fb : Nat → Bool) :
    val (fun k => mulBits wa fa wb fb k) w = val fa wa * val fb wb % 2 ^ w :=
  val_testBit _ w

theorem mulBits_congr {w : Nat} {f f' g g' : Nat → Bool} (hf : ∀ j, j < w → f j = f' j)
    (hg : ∀ j, j < w → g j = g' j) (k : Nat) : mulBits w f w g k = mulBits w f' w g' k := by
  simp only [mulBits, val_congr_lt hf, val_congr_lt hg]

/-- The sum of two bit functions is insensitive to the bits above the width. -/
theorem addBits_congr {w : Nat} {f f' g g' : Nat → Bool} (hf : ∀ j, j < w → f j = f' j)
    (hg : ∀ j, j < w → g j = g' j) (k : Nat) : addBits w f w g k = addBits w f' w g' k := by
  simp only [addBits, val_congr_lt hf, val_congr_lt hg]

theorem subBits_congr {w : Nat} {f f' g g' : Nat → Bool} (hf : ∀ j, j < w → f j = f' j)
    (hg : ∀ j, j < w → g j = g' j) (k : Nat) : subBits w f w g k = subBits w f' w g' k := by
  simp only [subBits, val_congr_lt hf, val_congr_lt hg]

/-- Bit `k` of the unsized constant `v` materialized at width `w` (`LVec.ofInt w v`). -/
def constBit (v : Int) (w k : Nat) : Bool := ((v.emod ((2 : Int) ^ w)).toNat).testBit k

/-- A zero-extended bit function read BELOW its width is the narrower vector (truncation). -/
theorem bv_zext_trunc {n m : Nat} (f : Nat → Bool) (h : m ≤ n) :
    bv m (zext n f) = (bv n f).setWidth m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_bv hi, BitVec.getLsbD_setWidth, getLsbD_bv (by omega)]
  simp [zext, hi, show i < n by omega]

/-- The unsized constant `v` at width `w` is `BitVec.ofInt w v`. -/
theorem bv_constBit (v : Int) (w : Nat) : bv w (constBit v w) = BitVec.ofInt w v := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_bv, BitVec.toNat_ofInt]
  unfold constBit
  rw [val_testBit, Nat.mod_eq_of_lt]
  · rfl
  · have hm : (0 : Int) < (2 : Int) ^ w := by exact_mod_cast Nat.two_pow_pos w
    have h1 : v % (2 : Int) ^ w < (2 : Int) ^ w := Int.emod_lt_of_pos v hm
    have h2 : 0 ≤ v % (2 : Int) ^ w := Int.emod_nonneg v (Int.ne_of_gt hm)
    have hne : 0 < 2 ^ w := Nat.two_pow_pos w
    have h3 : (v % (2 : Int) ^ w).toNat < 2 ^ w := by
      rw [Int.toNat_lt' hne]; exact_mod_cast h1
    exact h3

/-- An ordering of bit functions is the `BitVec` ordering. -/
theorem lt_bv {w : Nat} (f g : Nat → Bool) : decide (val f w < val g w) = decide (bv w f < bv w g) := by
  simp [BitVec.lt_def, toNat_bv]

theorem le_bv {w : Nat} (f g : Nat → Bool) : decide (val f w ≤ val g w) = decide (bv w f ≤ bv w g) := by
  simp [BitVec.le_def, toNat_bv]

/-- **Left-shift glue.** The bit equations of `a << s` (the left operand zero-extended to the context, the amount any
bit function) are `BitVec` shifting: an amount at least the width gives `0`, as in the LRM. -/
theorem bv_shlBits {w wl wr : Nat} (f g : Nat → Bool) :
    bv w (shlBits (zext wl f) wr g) = ((bv wl f).setWidth w) <<< (bv wr g).toNat := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_bv hk, BitVec.getLsbD_shiftLeft, toNat_bv, BitVec.getLsbD_setWidth]
  simp only [shlBits, zext]
  by_cases h1 : val g wr ≤ k
  · by_cases h2 : k - val g wr < wl
    · have h3 : (bv wl f).getLsbD (k - val g wr) = f (k - val g wr) := getLsbD_bv h2
      have h4 : k - val g wr < w := by omega
      rw [h3]
      simp [hk, h1, h2, h4]
    · have h3 : (bv wl f).getLsbD (k - val g wr) = false := BitVec.getLsbD_of_ge _ _ (by omega)
      rw [h3]
      simp [hk, h1, h2]
  · simp [hk, h1]

/-- **Left-shift glue for a left operand that is an operation**: the shift of any bit function `f`, read at `w` bits, is
`BitVec` shifting of `f`'s `w`-bit vector. (The left operand of a shift is computed at the shift's width, IEEE 1800-2023
§11.6.1, so the equation of `(a + b) << s` is `XF.shlBits` of the sum's bit function at that width.) -/
theorem bv_shlBits_gen {w wr : Nat} (f g : Nat → Bool) :
    bv w (shlBits f wr g) = (bv w f) <<< (bv wr g).toNat := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_bv hk, BitVec.getLsbD_shiftLeft, toNat_bv]
  simp only [shlBits]
  by_cases h1 : val g wr ≤ k
  · rw [getLsbD_bv (show k - val g wr < w by omega)]
    simp [hk, h1]
  · simp [hk, h1]

/-- A sign extension of the `BitVec` of a bit function is the `XF.sext` bit function. -/
theorem getLsbD_signExtend_bv {w wl : Nat} (f : Nat → Bool) {j : Nat} (hj : j < w) :
    ((bv wl f).signExtend w).getLsbD j = sext wl f j := by
  rw [BitVec.getLsbD_signExtend]
  by_cases h1 : j < wl
  · rw [getLsbD_bv h1]
    simp [sext, hj, h1]
  · have hmsb : (bv wl f).msb = (decide (0 < wl) && f (wl - 1)) := by
      by_cases h0 : 0 < wl
      · rw [BitVec.msb_eq_getLsbD_last, getLsbD_bv (show wl - 1 < wl by omega)]
        simp [h0]
      · have : wl = 0 := by omega
        subst this
        simp [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_of_ge]
    simp [sext, hj, h1, hmsb]

/-- **Signed left-shift glue** (`1 << s`: the left operand is a signed integer, extended by its sign bit). -/
theorem bv_shlBits_s {w wl wr : Nat} (f g : Nat → Bool) :
    bv w (shlBits (sext wl f) wr g) = ((bv wl f).signExtend w) <<< (bv wr g).toNat := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_bv hk, BitVec.getLsbD_shiftLeft, toNat_bv]
  simp only [shlBits]
  by_cases h1 : val g wr ≤ k
  · have h4 : k - val g wr < w := by omega
    rw [getLsbD_signExtend_bv f h4]
    simp [hk, h1]
  · simp [hk, h1]

/-! ### Concatenation operands (WP-B2 gate 3b) -/

/-- The bit function `sv_equations` prints for a zero pad above an `n`-bit operand, `if j < n then f j else false`, is the
zero extension. -/
theorem ite_zext (n : Nat) (f : Nat → Bool) : (fun j => if j < n then f j else false) = zext n f := by
  funext j; by_cases h : j < n <;> simp [zext, h]

/-- A zero pad above an `n`-bit operand, read at width `w ≥ n`: `BitVec` zero extension. -/
theorem bv_pad {w n : Nat} (h : n ≤ w) (f : Nat → Bool) :
    bv w (fun j => if j < n then f j else false) = (bv n f).setWidth w := by
  rw [ite_zext]
  exact bv_zext f h

/-- **Concatenation glue**: `{hi, lo}` as a bit function (`if j < w2 then lo j else hi (j - w2)`) is `BitVec` append. -/
theorem bv_cat2 {w1 w2 : Nat} (hi lo : Nat → Bool) :
    bv (w1 + w2) (fun j => if j < w2 then lo j else hi (j - w2)) = bv w1 hi ++ bv w2 lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_bv hk, BitVec.getLsbD_append]
  by_cases h : k < w2
  · rw [if_pos h, if_pos h, getLsbD_bv h]
  · rw [if_neg h, if_neg h, getLsbD_bv (show k - w2 < w1 by omega)]

/-- **Right-shift glue.** -/
theorem bv_shrBits {w wl wr : Nat} (f g : Nat → Bool) :
    bv w (shrBits wl f wr g) = ((bv wl f) >>> (bv wr g).toNat).setWidth w := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_bv hk, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, toNat_bv]
  simp only [shrBits]
  by_cases h2 : k + val g wr < wl
  · have h3 : (bv wl f).getLsbD (val g wr + k) = f (k + val g wr) := by
      rw [Nat.add_comm]; exact getLsbD_bv h2
    rw [h3]
    simp [hk, h2]
  · have h3 : (bv wl f).getLsbD (val g wr + k) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    rw [h3]
    simp [hk, h2]

/-- A `w`-bit bit function sign-extended to `w` bits reads as itself. -/
theorem bv_sext_self {w : Nat} (f : Nat → Bool) : bv w (sext w f) = bv w f :=
  bv_congr_lt (fun k hk => by simp [sext, hk])

/-- **Arithmetic-shift glue** (IEEE 1800-2023 §11.4.10): `XF.ashrBits`, the equation of `>>>` over a signed operand, is
`BitVec.sshiftRight` by the amount read as a natural number (an amount of `w` or more fills every bit with the sign). -/
theorem bv_ashrBits {w wr : Nat} (f g : Nat → Bool) :
    bv w (ashrBits w f wr g) = (bv w f).sshiftRight (bv wr g).toNat := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_bv hk, BitVec.getLsbD_sshiftRight, toNat_bv]
  simp only [ashrBits]
  have hk' : ¬ w ≤ k := by omega
  by_cases h2 : k + val g wr < w
  · have h3 : (bv w f).getLsbD (val g wr + k) = f (k + val g wr) := by
      rw [Nat.add_comm]; exact getLsbD_bv h2
    have h4 : val g wr + k < w := by omega
    rw [if_pos h2, if_pos h4, h3]
    simp [hk']
  · have hmsb : (bv w f).msb = f (w - 1) := by
      rw [BitVec.msb_eq_getLsbD_last, getLsbD_bv (show w - 1 < w by omega)]
    have h4 : ¬ val g wr + k < w := by omega
    rw [if_neg h2, if_neg h4, hmsb]
    simp [hk', show 0 < w by omega]

end XF
end LeanModels.Sv

/-- info: 'LeanModels.Sv.XF.bv_addBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.XF.bv_addBits

/-- info: 'LeanModels.Sv.XF.bv_subBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.XF.bv_subBits

/-- info: 'LeanModels.Sv.XF.bv_zext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.XF.bv_zext

/-- info: 'LeanModels.Sv.XF.bv_ashrBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.XF.bv_ashrBits

/-- info: 'LeanModels.Sv.XF.bv_shlBits_gen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.XF.bv_shlBits_gen
