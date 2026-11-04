/-!
# `LeanModels.Sv.Lib.BitVecArith`: `BitVec` arithmetic for datapath proofs (no imports)

Facts about core's `BitVec` that register-transfer proofs keep needing and core does not state in this form:

* `setWidth_signExtend_of_le`: truncating a sign extension to a narrower width is the narrower sign extension;
* `setWidth_add_mul_signExtend`: a multiply-accumulate computed at a wider width and truncated back is the
  accumulate of the operands' signed product (`ofInt` of the product of `toInt`s);
* `extractLsb'_ushiftRight`: a part select of a logical right shift is a part select of the operand;
* `ofNat_eq_ofNat_sub_one_iff`: a counter `t < N ≤ 2^w` compared with `N - 1` at `w` bits tests `t + 1 = N`.

Plain Lean (Init only): nothing here mentions an SV design. In namespace `LeanModels.Sv.Lib`, not `BitVec`, so a
later core or Mathlib lemma of the same name cannot clash.
-/

namespace LeanModels.Sv.Lib

/-- Truncating the sign extension of `y` to `n` bits down to `m ≤ n` bits is the sign extension to `m` bits. -/
theorem setWidth_signExtend_of_le {w m n : Nat} (y : BitVec w) (h : m ≤ n) :
    (y.signExtend n).setWidth m = y.signExtend m := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.getLsbD_signExtend, decide_eq_true hi,
    decide_eq_true (by omega : i < n), Bool.true_and, Bool.true_and]

/-- **One multiply-accumulate at a wider width**: `x + a·b` computed at `n ≥ m` bits (the accumulator
zero-extended, the operands sign-extended) and truncated back to `m` bits is `x + ofInt (a.toInt · b.toInt)` at
`m` bits. -/
theorem setWidth_add_mul_signExtend {m n w : Nat} (h : m ≤ n) (x : BitVec m) (a b : BitVec w) :
    (x.setWidth n + a.signExtend n * b.signExtend n).setWidth m = x + BitVec.ofInt m (a.toInt * b.toInt) := by
  rw [BitVec.setWidth_add _ _ h, BitVec.setWidth_mul _ _ h, BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq,
    setWidth_signExtend_of_le _ h, setWidth_signExtend_of_le _ h, BitVec.ofInt_mul]; rfl

/-- A part select `[lo +: w]` of `x >>> s` is the part select `[s + lo +: w]` of `x`. -/
theorem extractLsb'_ushiftRight {n : Nat} (x : BitVec n) (s lo w : Nat) :
    (x >>> s).extractLsb' lo w = x.extractLsb' (s + lo) w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [BitVec.getLsbD_ushiftRight, Nat.add_assoc]

/-- **A counter at its last value**: for `t < N ≤ 2^w`, `t = N - 1` at `w` bits exactly when `t + 1 = N`. At
`N = 2^w` (a full-range counter) the constant `N` is `0` at `w` bits and `0 - 1` wraps to `2^w - 1 = N - 1`. -/
theorem ofNat_eq_ofNat_sub_one_iff {w t N : Nat} (ht : t < N) (hN : N ≤ 2 ^ w) :
    BitVec.ofNat w t = BitVec.ofNat w N - 1#w ↔ t + 1 = N := by
  rw [← BitVec.toNat_inj, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rcases Nat.lt_or_eq_of_le hN with hN | rfl
  · rw [Nat.mod_eq_of_lt (by omega : t < 2 ^ w), Nat.mod_eq_of_lt (by omega : 1 < 2 ^ w),
      Nat.mod_eq_of_lt hN, show 2 ^ w - 1 + N = N - 1 + 2 ^ w by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : N - 1 < 2 ^ w)]
    omega
  · rw [Nat.mod_self, Nat.mod_eq_of_lt ht]
    by_cases hw : w = 0
    · subst hw; simp at ht ⊢ <;> omega
    · rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw), Nat.add_zero, Nat.mod_eq_of_lt (by omega)]; omega

end LeanModels.Sv.Lib
