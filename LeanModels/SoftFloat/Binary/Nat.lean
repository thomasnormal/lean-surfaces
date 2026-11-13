/-!
# Pure `Nat` facts for rounding and its certificates

Arithmetic the binary-format layer needs and core does not state: distances by truncated subtraction (`udist`), a
comparison with a Boolean strictness (`leB`), the round-to-nearest-even of a shifted quotient with its sticky bit
(`core_t`, `core_f`), the cross-multiplied interval bounds of a rounding certificate (`low_std` .. `up_lt_b`), and the
overflow-bit arithmetic of a datapath (`c0_of`, `thr_bound`).

`NatFacts` restates five lemmas of `LeanModels.Sv.Lib` (`log2_mul_two_pow`, `mul_pow_mul_pow`,
`mul_pow_mul_pow_mul_pow`, `scale_le` .. `scale_gt`) so that this language-neutral layer imports no SystemVerilog
module; it is a namespace of its own so that a proof which opens both libraries sees no ambiguous name. Imports core
only. Ported from the format-generic sections of svGolf's fdivp reference proof (the maintainers' text).
-/

namespace LeanModels.SoftFloat.Binary

namespace NatFacts

/-- Shifting a nonzero value left by `j` adds `j` to its `log2`. -/
theorem log2_mul_two_pow {e : Nat} (j : Nat) (he : e ≠ 0) : (e * 2 ^ j).log2 = e.log2 + j := by
  have h0 : e * 2 ^ j ≠ 0 := Nat.mul_ne_zero he (Nat.ne_of_gt (Nat.two_pow_pos _))
  rw [Nat.log2_eq_iff h0]
  constructor
  · rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ (Nat.log2_self_le he)
  · rw [show e.log2 + j + 1 = (e.log2 + 1) + j by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.two_pow_pos _)

/-- Two factors that are powers of one base `b` collect into one power: `x·b^m·b^n = x·b^(m+n)`. -/
theorem mul_pow_mul_pow (x b m n : Nat) : x * b ^ m * b ^ n = x * b ^ (m + n) := by
  rw [Nat.mul_assoc, ← Nat.pow_add]

/-- Three factors that are powers of one base `b` collect into one power: `x·b^l·b^m·b^n = x·b^(l+m+n)`. -/
theorem mul_pow_mul_pow_mul_pow (x b l m n : Nat) : x * b ^ l * b ^ m * b ^ n = x * b ^ (l + m + n) := by
  simp only [Nat.pow_add, Nat.mul_assoc]

/-- With `N * S = D * T`: `D * X ≤ N` (`X ≤ N / D`) exactly when `S * X ≤ T` (`X ≤ T / S`). -/
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

/-- With `N * S = D * T`: `N ≤ D * X` (`N / D ≤ X`) exactly when `T ≤ S * X` (`T / S ≤ X`). -/
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

/-- With `N * S = D * T`: `D * X < N` (`X < N / D`) exactly when `S * X < T` (`X < T / S`). -/
theorem scale_lt (D S N T X : Nat) (hD : 0 < D) (hS : 0 < S) (h : N * S = D * T) :
    (D * X < N ↔ S * X < T) := by
  have := scale_ge D S N T X hD hS h
  omega

/-- With `N * S = D * T`: `N < D * X` (`N / D < X`) exactly when `T < S * X` (`T / S < X`). -/
theorem scale_gt (D S N T X : Nat) (hD : 0 < D) (hS : 0 < S) (h : N * S = D * T) :
    (N < D * X ↔ T < S * X) := by
  have := scale_le D S N T X hD hS h
  omega

end NatFacts

/-- `|u·D − N|` in `Nat` (one of the two truncated differences is 0). -/
def udist (N D u : Nat) : Nat := (N - u * D) + (u * D - N)

/-- `x ≤ y`, strict unless `par` (the certificate's "equality only for an even significand"). -/
def leB (par : Bool) (x y : Nat) : Prop := if par = true then x ≤ y else x < y

theorem leB_of_eq {par : Bool} (hp : par = true) (x y : Nat) : leB par x y = (x ≤ y) := by
  simp [leB, hp]

theorem leB_of_ne {par : Bool} (hp : ¬ par = true) (x y : Nat) : leB par x y = (x < y) := by
  simp [leB, hp]

theorem ite_decide_leB (q : Prop) [Decidable q] (x y : Nat) :
    ((if q then decide (x ≤ y) else decide (x < y)) = true) ↔ leB (decide q) x y := by
  by_cases h : q <;> simp [leB, h]

theorem two_zP_sub (z P y : Nat) (hy : y + 1 = 2 * z) : 2 * (z * P) - P = y * P := by
  have h : 2 * (z * P) = y * P + P := by
    calc 2 * (z * P) = (2 * z) * P := by rw [Nat.mul_assoc]
      _ = (y + 1) * P := by rw [hy]
      _ = y * P + P := by rw [Nat.add_mul, Nat.one_mul]
  omega

theorem two_zP_add (z P y : Nat) (hy : y = 2 * z + 1) : 2 * (z * P) + P = y * P := by
  subst hy
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]

/-- Lower bound, distance `P` below `u`. -/
theorem low_std (nb M P y z qm M0 : Nat) (hy : y + 1 = 2 * z) (hX : y * M ≤ 2 * qm) (hq : nb * qm ≤ M0) :
    (nb * M) * (2 * (z * P) - P) ≤ 2 * (P * M0) := by
  rw [two_zP_sub z P y hy]
  calc (nb * M) * (y * P) = P * (nb * (y * M)) := by ac_rfl
    _ ≤ P * (nb * (2 * qm)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hX)
    _ = P * (2 * (nb * qm)) := by ac_rfl
    _ ≤ P * (2 * M0) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (P * M0) := by ac_rfl

/-- ... strict, from a strict `qm`-side bound. -/
theorem low_std_lt_a (nb M P y z qm M0 : Nat) (hnb : 0 < nb) (hP : 0 < P) (hy : y + 1 = 2 * z)
    (hX : y * M < 2 * qm) (hq : nb * qm ≤ M0) : (nb * M) * (2 * (z * P) - P) < 2 * (P * M0) := by
  rw [two_zP_sub z P y hy]
  calc (nb * M) * (y * P) = P * (nb * (y * M)) := by ac_rfl
    _ < P * (nb * (2 * qm)) := Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left hX hnb) hP
    _ = P * (2 * (nb * qm)) := by ac_rfl
    _ ≤ P * (2 * M0) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (P * M0) := by ac_rfl

/-- ... strict, from a strict `M0`-side bound (the sticky bit is set). -/
theorem low_std_lt_b (nb M P y z qm M0 : Nat) (hP : 0 < P) (hy : y + 1 = 2 * z)
    (hX : y * M ≤ 2 * qm) (hq : nb * qm < M0) : (nb * M) * (2 * (z * P) - P) < 2 * (P * M0) := by
  rw [two_zP_sub z P y hy]
  calc (nb * M) * (y * P) = P * (nb * (y * M)) := by ac_rfl
    _ ≤ P * (nb * (2 * qm)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hX)
    _ = P * (2 * (nb * qm)) := by ac_rfl
    _ < P * (2 * M0) := Nat.mul_lt_mul_of_pos_left (by omega) hP
    _ = 2 * (P * M0) := by ac_rfl

/-- Lower bound at a binade bottom, where the result is the floor (`z·M ≤ qm`): any distance below. -/
theorem low_floor (nb M P z qm M0 dn : Nat) (hX : z * M ≤ qm) (hq : nb * qm ≤ M0) :
    (nb * M) * (2 * (z * P) - dn) ≤ 2 * (P * M0) := by
  calc (nb * M) * (2 * (z * P) - dn) ≤ (nb * M) * (2 * (z * P)) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = 2 * (P * (nb * (z * M))) := by ac_rfl
    _ ≤ 2 * (P * (nb * qm)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left P (Nat.mul_le_mul_left nb hX))
    _ ≤ 2 * (P * M0) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left P hq)

/-- Upper bound (non-strict): `2·M0 ≤ nb·(y'·M)` from `2·qm ≤ y'·M` and `M0 ≤ nb·qm`. -/
theorem up_le (nb M P y' z qm M0 : Nat) (hy : y' = 2 * z + 1) (hX : 2 * qm ≤ y' * M) (hq : M0 ≤ nb * qm) :
    2 * (P * M0) ≤ (nb * M) * (2 * (z * P) + P) := by
  rw [two_zP_add z P y' hy]
  calc 2 * (P * M0) ≤ 2 * (P * (nb * qm)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left P hq)
    _ = P * (nb * (2 * qm)) := by ac_rfl
    _ ≤ P * (nb * (y' * M)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hX)
    _ = (nb * M) * (y' * P) := by ac_rfl

/-- ... strict from the core's strict inequality. -/
theorem up_lt_a (nb M P y' z qm M0 : Nat) (hnb : 0 < nb) (hP : 0 < P) (hy : y' = 2 * z + 1)
    (hX : 2 * qm < y' * M) (hq : M0 ≤ nb * qm) : 2 * (P * M0) < (nb * M) * (2 * (z * P) + P) := by
  rw [two_zP_add z P y' hy]
  calc 2 * (P * M0) ≤ 2 * (P * (nb * qm)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left P hq)
    _ = P * (nb * (2 * qm)) := by ac_rfl
    _ < P * (nb * (y' * M)) := Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left hX hnb) hP
    _ = (nb * M) * (y' * P) := by ac_rfl

/-- ... strict from the sticky bit: `M0 < nb·qm + nb` and `2·qm + 2 ≤ y'·M`. -/
theorem up_lt_b (nb M P y' z qm M0 : Nat) (hnb : 0 < nb) (hP : 0 < P) (hy : y' = 2 * z + 1)
    (hX : 2 * qm + 2 ≤ y' * M) (hq : M0 < nb * qm + nb) :
    2 * (P * M0) < (nb * M) * (2 * (z * P) + P) := by
  rw [two_zP_add z P y' hy]
  have e1 : nb * (2 * qm) = 2 * (nb * qm) := by ac_rfl
  have h1 : 2 * M0 < nb * (2 * qm + 2) := by
    calc 2 * M0 < 2 * (nb * qm + nb) := by omega
      _ = nb * (2 * qm + 2) := by rw [Nat.mul_add nb (2 * qm) 2, e1, Nat.mul_add 2 (nb * qm) nb]; omega
  calc 2 * (P * M0) = P * (2 * M0) := by ac_rfl
    _ < P * (nb * (2 * qm + 2)) := Nat.mul_lt_mul_of_pos_left h1 hP
    _ ≤ P * (nb * (y' * M)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hX)
    _ = (nb * M) * (y' * P) := by ac_rfl

/-- The distance (in units) from `uF E T` down to the previous representable magnitude. -/
def dnF (E T : Nat) : Nat := if 2 ≤ E ∧ T = 0 then 2 ^ (E - 1 - 1) else 2 ^ (E - 1)

theorem mul2_le (S u v c : Nat) (h : c ≤ u) : c * (S * 2) ≤ 2 * (S * u + v) := by
  have h1 : c * (S * 2) ≤ u * (S * 2) := Nat.mul_le_mul_right _ h
  have h2 : u * (S * 2) = 2 * (S * u) := by ac_rfl
  omega

theorem mul2_lt (S u v c : Nat) (h : c < u ∨ (c = u ∧ 0 < v)) (hS : 0 < S) :
    c * (S * 2) < 2 * (S * u + v) := by
  rcases h with h | ⟨rfl, hv⟩
  · have h1 : (c + 1) * (S * 2) ≤ u * (S * 2) := Nat.mul_le_mul_right _ h
    have h2 : u * (S * 2) = 2 * (S * u) := by ac_rfl
    have h3 : (c + 1) * (S * 2) = c * (S * 2) + S * 2 := by rw [Nat.add_mul, Nat.one_mul]
    omega
  · have h2 : c * (S * 2) = 2 * (S * c) := by ac_rfl
    omega

theorem lt_mul2 (S u v c : Nat) (hv : v < S) (h : u + 1 ≤ c) : 2 * (S * u + v) < c * (S * 2) := by
  have h1 : (u + 1) * (S * 2) ≤ c * (S * 2) := Nat.mul_le_mul_right _ h
  have h2 : (u + 1) * (S * 2) = 2 * (S * u) + S * 2 := by
    rw [Nat.add_mul, Nat.one_mul]
    have : u * (S * 2) = 2 * (S * u) := by ac_rfl
    omega
  omega

theorem lt2_mul2 (S u v c : Nat) (hv : v < S) (h : u + 1 ≤ c) : 2 * (S * u + v) + 2 ≤ c * (S * 2) := by
  have h1 : (u + 1) * (S * 2) ≤ c * (S * 2) := Nat.mul_le_mul_right _ h
  have h2 : (u + 1) * (S * 2) = 2 * (S * u) + S * 2 := by
    rw [Nat.add_mul, Nat.one_mul]
    have : u * (S * 2) = 2 * (S * u) := by ac_rfl
    omega
  omega

theorem le_mul2 (S u v c : Nat) (hv : v < S) (h : u + 1 ≤ c ∨ (c = u ∧ v = 0)) :
    2 * (S * u + v) ≤ c * (S * 2) := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact Nat.le_of_lt (lt_mul2 S u v c hv h)
  · have h2 : c * (S * 2) = 2 * (S * c) := by ac_rfl
    omega

/-- `st0 = true`: `inc = rb`, so `z = (qs + 1) / 2`; `z` is within half a spacing on both sides, strictly above
(the true value is strictly above `qm / 2^sh`). `M = 2^(sh+1)`. -/
theorem core_t (qm sh z : Nat) (hz : z = (qm / 2 ^ sh + 1) / 2) :
    (z = 0 ∨ (2 * z - 1) * 2 ^ (sh + 1) ≤ 2 * qm) ∧ 2 * qm + 2 ≤ (2 * z + 1) * 2 ^ (sh + 1) := by
  have hS : 0 < 2 ^ sh := Nat.two_pow_pos sh
  have hd := Nat.div_add_mod qm (2 ^ sh)
  have hv := Nat.mod_lt qm hS
  rw [Nat.pow_succ]
  generalize 2 ^ sh = S at *
  generalize qm / S = u at *
  generalize qm % S = v at *
  subst hd
  constructor
  · by_cases h0 : z = 0
    · exact Or.inl h0
    · exact Or.inr (mul2_le S u v (2 * z - 1) (by omega))
  · exact lt2_mul2 S u v (2 * z + 1) hv (by omega)

/-- `st0 = false`: `inc = rb ∧ (dropped bits nonzero ∨ qs[1])`; ties (the true value exactly half) round to even. -/
theorem core_f (qm sh z : Nat)
    (hz : ((qm / 2 ^ sh % 2 = 1 ∧ (qm % 2 ^ sh ≠ 0 ∨ qm / 2 ^ sh / 2 % 2 = 1)) ∧
            z = qm / 2 ^ sh / 2 + 1) ∨
          (¬ (qm / 2 ^ sh % 2 = 1 ∧ (qm % 2 ^ sh ≠ 0 ∨ qm / 2 ^ sh / 2 % 2 = 1)) ∧
            z = qm / 2 ^ sh / 2)) :
    (z = 0 ∨ ((2 * z - 1) * 2 ^ (sh + 1) ≤ 2 * qm ∧ (z % 2 = 1 → (2 * z - 1) * 2 ^ (sh + 1) < 2 * qm))) ∧
    2 * qm ≤ (2 * z + 1) * 2 ^ (sh + 1) ∧ (z % 2 = 1 → 2 * qm < (2 * z + 1) * 2 ^ (sh + 1)) := by
  have hS : 0 < 2 ^ sh := Nat.two_pow_pos sh
  have hd := Nat.div_add_mod qm (2 ^ sh)
  have hv := Nat.mod_lt qm hS
  rw [Nat.pow_succ]
  generalize 2 ^ sh = S at *
  generalize qm / S = u at *
  generalize qm % S = v at *
  subst hd
  have hz' : (u % 2 = 1 ∧ (v ≠ 0 ∨ u / 2 % 2 = 1) ∧ z = u / 2 + 1) ∨
      (¬ (u % 2 = 1 ∧ (v ≠ 0 ∨ u / 2 % 2 = 1)) ∧ z = u / 2) := by
    rcases hz with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · by_cases h0 : z = 0
    · exact Or.inl h0
    · refine Or.inr ⟨mul2_le S u v (2 * z - 1) ?_, fun hodd => mul2_lt S u v (2 * z - 1) ?_ hS⟩
      · omega
      · omega
  · apply le_mul2 S u v (2 * z + 1) hv
    omega
  · intro hodd
    exact lt_mul2 S u v (2 * z + 1) hv (by omega)

theorem c0_of (nb M P qm M0 Th : Nat) (hnb : 0 < nb) (hP : 0 < P) (hq : M0 < nb * qm + nb)
    (hb : P * (qm + 1) ≤ M * Th) : P * M0 < (nb * M) * Th := by
  have h1 : M0 < nb * (qm + 1) := by rw [Nat.mul_add]; omega
  calc P * M0 < P * (nb * (qm + 1)) := Nat.mul_lt_mul_of_pos_left h1 hP
    _ = nb * (P * (qm + 1)) := by ac_rfl
    _ ≤ nb * (M * Th) := Nat.mul_le_mul_left _ hb
    _ = (nb * M) * Th := by ac_rfl

/-- The below-threshold inequality `P·(qm+1) ≤ M·Th` with `Th = (A-1)·Q` in the three regimes of the datapath. -/
theorem thr_bound (A Q P qm M : Nat) (hQ : 0 < Q) (hA : 8 ≤ A)
    (h : (M = 2 ∧ P ≤ Q ∧ qm + 1 ≤ A) ∨ (M = 2 ∧ P = 2 * Q ∧ qm + 1 ≤ A - 1) ∨
      (4 ≤ M ∧ P = 1 ∧ qm + 1 ≤ A)) :
    P * (qm + 1) ≤ M * ((A - 1) * Q) := by
  rcases h with ⟨rfl, h1, h2⟩ | ⟨rfl, rfl, h2⟩ | ⟨h1, rfl, h2⟩
  · calc P * (qm + 1) ≤ Q * A := Nat.mul_le_mul h1 h2
      _ = A * Q := Nat.mul_comm _ _
      _ ≤ (2 * (A - 1)) * Q := Nat.mul_le_mul_right Q (by omega)
      _ = 2 * ((A - 1) * Q) := Nat.mul_assoc _ _ _
  · calc 2 * Q * (qm + 1) ≤ 2 * Q * (A - 1) := Nat.mul_le_mul_left _ h2
      _ = 2 * ((A - 1) * Q) := by ac_rfl
  · have h3 : A - 1 ≤ (A - 1) * Q := Nat.le_mul_of_pos_right _ hQ
    have h4 : 4 * ((A - 1) * Q) ≤ M * ((A - 1) * Q) := Nat.mul_le_mul_right _ h1
    omega

end LeanModels.SoftFloat.Binary
