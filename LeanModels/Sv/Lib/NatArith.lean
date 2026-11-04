/-!
# `LeanModels.Sv.Lib.NatArith`: `Nat` arithmetic for word-level proofs (no imports)

Facts about `Nat` that word-level datapath proofs keep needing and core does not state in this form: the
`log2` of a shifted value, products of powers of two, inequalities scaled by a common factor (a fraction
`N / D` compared with `T / S` when `N * S = D * T`), a reduction modulo `2^w` inside a wider context, a
decrement modulo `Z`, quotient and remainder by uniqueness, the three bands of `x < 3 * Z`, the top bit
of a value below `2 * H`, and the split of a remainder at a power of two.

Plain Lean (Init only): nothing here mentions an SV design. Proved by `omega` and core lemmas.
-/

namespace LeanModels.Sv.Lib

theorem log2_mul_pow {e : Nat} (j : Nat) (he : e ≠ 0) : (e * 2 ^ j).log2 = e.log2 + j := by
  have h0 : e * 2 ^ j ≠ 0 := Nat.mul_ne_zero he (Nat.ne_of_gt (Nat.two_pow_pos _))
  rw [Nat.log2_eq_iff h0]
  constructor
  · rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ (Nat.log2_self_le he)
  · rw [show e.log2 + j + 1 = (e.log2 + 1) + j by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.two_pow_pos _)

theorem mul_pow3 (x a1 a2 a3 : Nat) : x * 2 ^ a1 * 2 ^ a2 * 2 ^ a3 = x * 2 ^ (a1 + a2 + a3) := by
  simp only [Nat.pow_add, Nat.mul_assoc]

theorem mul_pow2 (x a1 a2 : Nat) : x * 2 ^ a1 * 2 ^ a2 = x * 2 ^ (a1 + a2) := by
  simp only [Nat.pow_add, Nat.mul_assoc]

/-! ## Scaled comparisons: with `N * S = D * T`, `X` against `N / D` is `X` against `T / S` -/

theorem scale_le (D S N T X : Nat) (hD : 0 < D) (hS : 0 < S) (h : N * S = D * T) :
    (D * X ≤ N ↔ S * X ≤ T) := by
  constructor
  · intro hh
    have h1 : D * X * S ≤ N * S := Nat.mul_le_mul_right S hh
    rw [h] at h1
    have h2 : D * (S * X) ≤ D * T := by
      calc D * (S * X) = D * X * S := by ac_rfl
        _ ≤ D * T := h1
    exact Nat.le_of_mul_le_mul_left h2 hD
  · intro hh
    have h1 : D * (S * X) ≤ D * T := Nat.mul_le_mul_left D hh
    have h2 : D * X * S ≤ N * S := by
      rw [h]
      calc D * X * S = D * (S * X) := by ac_rfl
        _ ≤ D * T := h1
    exact Nat.le_of_mul_le_mul_right h2 hS

theorem scale_ge (D S N T X : Nat) (hD : 0 < D) (hS : 0 < S) (h : N * S = D * T) :
    (N ≤ D * X ↔ T ≤ S * X) := by
  constructor
  · intro hh
    have h1 : N * S ≤ D * X * S := Nat.mul_le_mul_right S hh
    rw [h] at h1
    have h2 : D * T ≤ D * (S * X) := by
      calc D * T ≤ D * X * S := h1
        _ = D * (S * X) := by ac_rfl
    exact Nat.le_of_mul_le_mul_left h2 hD
  · intro hh
    have h1 : D * T ≤ D * (S * X) := Nat.mul_le_mul_left D hh
    have h2 : N * S ≤ D * X * S := by
      rw [h]
      calc D * T ≤ D * (S * X) := h1
        _ = D * X * S := by ac_rfl
    exact Nat.le_of_mul_le_mul_right h2 hS

theorem scale_lt (D S N T X : Nat) (hD : 0 < D) (hS : 0 < S) (h : N * S = D * T) :
    (D * X < N ↔ S * X < T) := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hc => ?_
    have hc' : T ≤ S * X := Nat.le_of_not_lt hc
    have : N ≤ D * X := (scale_ge D S N T X hD hS h).2 hc'
    omega
  · intro hh
    refine Classical.byContradiction fun hc => ?_
    have hc' : N ≤ D * X := Nat.le_of_not_lt hc
    have : T ≤ S * X := (scale_ge D S N T X hD hS h).1 hc'
    omega

theorem scale_gt (D S N T X : Nat) (hD : 0 < D) (hS : 0 < S) (h : N * S = D * T) :
    (N < D * X ↔ T < S * X) := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hc => ?_
    have hc' : S * X ≤ T := Nat.le_of_not_lt hc
    have : D * X ≤ N := (scale_le D S N T X hD hS h).2 hc'
    omega
  · intro hh
    refine Classical.byContradiction fun hc => ?_
    have hc' : D * X ≤ N := Nat.le_of_not_lt hc
    have : S * X ≤ T := (scale_le D S N T X hD hS h).1 hc'
    omega

theorem mullt (k x y : Nat) (hk : 0 < k) (h : x < y) : k * x < k * y := by
  first
    | exact (Nat.mul_lt_mul_left hk).2 h
    | exact Nat.mul_lt_mul_of_pos_left h hk
    | (apply Nat.lt_of_not_ge; intro hh; have := Nat.le_of_mul_le_mul_left hh hk; omega)

/-! ## Modular facts -/

/-- `(a - 1)` at width `w` inside a context of width `M >= w`, as a register decrement. -/
theorem mod_wrap (y c w M : Nat) (hc2 : c ≤ 2 ^ w) (hM : w ≤ M) :
    (y + (2 ^ M - c)) % 2 ^ w = (y + (2 ^ w - c)) % 2 ^ w := by
  obtain ⟨m, rfl⟩ : ∃ m, M = w + m := ⟨M - w, by omega⟩
  have h1 : 2 ^ (w + m) = 2 ^ w * 2 ^ m := Nat.pow_add _ _ _
  have h2 : 1 ≤ 2 ^ m := Nat.two_pow_pos m
  have h3 : 2 ^ w * 1 ≤ 2 ^ w * 2 ^ m := Nat.mul_le_mul_left _ h2
  have h4 : 2 ^ w * (2 ^ m - 1) = 2 ^ w * 2 ^ m - 2 ^ w := Nat.mul_sub_one _ _
  have e : y + (2 ^ (w + m) - c) = (y + (2 ^ w - c)) + 2 ^ w * (2 ^ m - 1) := by omega
  rw [e, Nat.add_mul_mod_self_left]

/-- A decrement modulo `Z`: `y - 1`, wrapping `0` to `Z - 1`. -/
theorem ydec_eq (Z y : Nat) (hy : y < Z) : (y + (Z - 1)) % Z = if y = 0 then Z - 1 else y - 1 := by
  by_cases h0 : y = 0
  · subst h0
    rw [if_pos rfl, Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [if_neg h0]
    have e : y + (Z - 1) = (y - 1) + Z := by omega
    rw [e, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

/-- Quotient and remainder by uniqueness. -/
theorem divmod_unique (Mt Ec Tc mag : Nat) (hMt : 0 < Mt) (hT : Tc < Mt) (h : mag = Ec * Mt + Tc) :
    mag / Mt = Ec ∧ mag % Mt = Tc := by
  subst h
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hMt, Nat.div_eq_of_lt hT, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hT]

/-- The three bands of `x < 3 * Z` and `x % Z` in each. -/
theorem mod3 (x Z : Nat) (hZ : 0 < Z) (hx : x < 3 * Z) :
    (x % Z = x ∧ x < Z) ∨ (x % Z + Z = x ∧ Z ≤ x ∧ x < 2 * Z) ∨ (x % Z + 2 * Z = x ∧ 2 * Z ≤ x) := by
  by_cases h1 : x < Z
  · exact Or.inl ⟨Nat.mod_eq_of_lt h1, h1⟩
  · by_cases h2 : x < 2 * Z
    · right; left
      have e1 : x % Z = (x - Z) % Z := Nat.mod_eq_sub_mod (by omega)
      rw [e1, Nat.mod_eq_of_lt (by omega)]
      omega
    · right; right
      have e1 : x % Z = (x - Z) % Z := Nat.mod_eq_sub_mod (by omega)
      have e2 : (x - Z) % Z = (x - Z - Z) % Z := Nat.mod_eq_sub_mod (by omega)
      rw [e1, e2, Nat.mod_eq_of_lt (by omega)]
      omega

/-- The top bit of a value below `2 * H` is the test `H ≤ x`. -/
theorem bit_top (x H : Nat) (hH : 0 < H) (hx : x < 2 * H) : (x / H % 2 = 0 ↔ x < H) := by
  by_cases h : x < H
  · have e : x / H = 0 := Nat.div_eq_of_lt h
    rw [e]; simp [h]
  · have h1 : 1 ≤ x / H := (Nat.le_div_iff_mul_le hH).2 (by omega)
    have h2 : x / H < 2 := (Nat.div_lt_iff_lt_mul hH).2 (by omega)
    have e : x / H = 1 := by omega
    rw [e]; simp [h]

/-- The remainder modulo `2 * u` is the remainder modulo `u` plus bit `u` of the quotient by `u`. -/
theorem frac_split (m u : Nat) (hu : 0 < u) :
    m / (2 * u) * (2 * u) + (if m / u % 2 = 1 then 1 else 0) * u + m % u =
      m / (2 * u) * (2 * u) + m % (2 * u) := by
  have h1 : m / (2 * u) = m / u / 2 := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  have h2 := Nat.div_add_mod m u
  have h3 := Nat.mod_lt m hu
  have h5 := Nat.div_add_mod m (2 * u)
  rw [h1] at h5 ⊢
  have h4 := Nat.div_add_mod (m / u) 2
  generalize m / u = q at *
  generalize m % u = r at *
  generalize m % (2 * u) = s at *
  generalize q / 2 = w at *
  have e0 : w * (2 * u) = (2 * u) * w := Nat.mul_comm _ _
  have e1 : u * q = (2 * u) * w + u * (q % 2) := by
    calc u * q = u * (2 * w + q % 2) := by rw [h4]
      _ = u * (2 * w) + u * (q % 2) := Nat.mul_add _ _ _
      _ = (2 * u) * w + u * (q % 2) := by ac_rfl
  by_cases hq : q % 2 = 1
  · rw [if_pos hq]
    rw [hq] at e1
    omega
  · rw [if_neg hq]
    have hq0 : q % 2 = 0 := by omega
    rw [hq0] at e1
    omega

end LeanModels.Sv.Lib
