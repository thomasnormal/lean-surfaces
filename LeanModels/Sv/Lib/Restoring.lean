import LeanModels.Sv.Lib.XFVal

/-!
# `LeanModels.Sv.Lib.Restoring`: restoring division

The partial remainders (`restRem`) and the quotient bits (`restQuo`) of restoring division, one quotient bit per
step: a step subtracts the divisor when it fits, then doubles. `restore_spec`: from a partial remainder `x < 2 * d`,
`n + 1` steps give the quotient `⌊2^n * x / d⌋` and the remainder `2 * (2^n * x mod d)`. `val_restQuo`: the quotient
bits of a hardware row, step `j`'s bit at position `n - 1 - j`, have the value `restQuo`.
-/

namespace LeanModels.Sv.Lib

/-- The partial remainder after `i` steps of restoring division of `x` by `d`: a step subtracts `d` when it
fits, then doubles. -/
def restRem (d x : Nat) : Nat → Nat
  | 0 => x
  | i + 1 => if d ≤ restRem d x i then 2 * (restRem d x i - d) else 2 * restRem d x i

/-- The quotient bits after `i` steps, most significant first, as a number (bit `i - 1 - j` is step `j`'s
bit). -/
def restQuo (d x : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => 2 * restQuo d x i + (if d ≤ restRem d x i then 1 else 0)

/-- The invariant of restoring division from `x < 2·d`: after `i` steps the partial remainder stays below `2·d`
and `restRem + 2·d·restQuo = 2^i·x`. -/
theorem restore_inv (d x : Nat) (hx : x < 2 * d) :
    ∀ i, restRem d x i < 2 * d ∧ restRem d x i + 2 * (d * restQuo d x i) = 2 ^ i * x
  | 0 => by simp [restRem, restQuo]; omega
  | i + 1 => by
    obtain ⟨h1, h2⟩ := restore_inv d x hx i
    have hp : 2 ^ (i + 1) * x = 2 * (2 ^ i * x) := by rw [Nat.pow_succ]; rw [Nat.mul_comm (2 ^ i) 2, Nat.mul_assoc]
    by_cases hb : d ≤ restRem d x i
    · have hq : d * (2 * restQuo d x i + 1) = 2 * (d * restQuo d x i) + d := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
      simp only [restRem, restQuo, hb, if_true, hq, hp]
      omega
    · have hq : d * (2 * restQuo d x i + 0) = 2 * (d * restQuo d x i) := by
        rw [Nat.add_zero, Nat.mul_left_comm]
      simp only [restRem, restQuo, hb, if_false, hq, hp]
      omega

/-- **Restoring division.** From a partial remainder `x < 2·d`, `n + 1` steps give the quotient `⌊2^n·x / d⌋`
and the remainder `2·(2^n·x mod d)`. -/
theorem restore_spec (d x n : Nat) (hd : 0 < d) (hx : x < 2 * d) :
    restQuo d x (n + 1) = 2 ^ n * x / d ∧ restRem d x (n + 1) = 2 * (2 ^ n * x % d) := by
  obtain ⟨h1, h2⟩ := restore_inv d x hx (n + 1)
  have hp : 2 ^ (n + 1) * x = 2 * (2 ^ n * x) := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]
  obtain ⟨r, hr⟩ : ∃ r, restRem d x (n + 1) = 2 * r := by
    simp only [restRem]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  rw [hr] at h1 h2 ⊢
  have hu : 2 ^ n * x / d = restQuo d x (n + 1) ∧ 2 ^ n * x % d = r :=
    (Nat.div_mod_unique hd).mpr ⟨by omega, by omega⟩
  exact ⟨hu.1.symm, by rw [hu.2]⟩

/-- The quotient bits as a hardware row (step `j`'s bit at position `n - 1 - j`) have the value `restQuo`. -/
theorem val_restQuo (d x : Nat) : ∀ n, XF.val (fun k => decide (d ≤ restRem d x (n - 1 - k))) n = restQuo d x n
  | 0 => by simp [XF.val, restQuo]
  | n + 1 => by
    have ih := val_restQuo d x n
    rw [XF.val_succ_low]
    have e : XF.val (fun k => decide (d ≤ restRem d x (n + 1 - 1 - (k + 1)))) n = restQuo d x n := by
      rw [← ih]
      apply XF.val_congr_lt
      intro j hj
      show decide (d ≤ restRem d x (n + 1 - 1 - (j + 1))) = decide (d ≤ restRem d x (n - 1 - j))
      have e1 : n + 1 - 1 - (j + 1) = n - 1 - j := by omega
      rw [e1]
    have e3 : n + 1 - 1 - 0 = n := by omega
    rw [e, e3]
    have hdec : (decide (d ≤ restRem d x n)).toNat = if d ≤ restRem d x n then 1 else 0 := by
      by_cases h : d ≤ restRem d x n <;> simp [h]
    rw [hdec]
    show _ = 2 * restQuo d x n + (if d ≤ restRem d x n then 1 else 0)
    omega

end LeanModels.Sv.Lib
