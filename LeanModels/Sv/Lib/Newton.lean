import LeanModels.Sv.Lib.Restoring
import LeanModels.Sv.Param

/-!
# `LeanModels.Sv.Lib.Newton`: Newton-Raphson division

The core of a Newton-Raphson divider of normalized significands `ma, mb ∈ [2^(P-1), 2^P)`, as the `Nat` values the
hardware computes (each product at its declared width, each part select a window), with `F = P + 4` fraction bits for
the reciprocal `r ≈ 2^F / d`, `d = mb / 2^(P-1) ∈ [1, 2)`:

* `nwR0`: the initial reciprocal `45/32 - 15/32·d`, that is `45·2^(P-1) - 15·mb`;
* `nwU`, `nwStep`: one step `r ← r·(2 - d·r)`: `u` is the one's complement of the top `F + 1` bits of `mb·r` (taken
  at `P + F` bits), and the product `r·u` (at `2F + 1` bits) is truncated to `F` fraction bits; `nwIter`: `k` steps;
* `nwQf`: the estimate `⌊ma·r / 2^(F-2)⌋` (`ma·r` at `P + F` bits); `nwRm`: the remainder `2^(P+1)·ma - qf·mb`
  modulo `2^(P+2)`; `nwQQ`, `nwRnz`: the quotient `qf + [rm ≥ mb] + [rm ≥ 2·mb]` and the sticky `rm ∉ {0, mb, 2·mb}`.

`newton_div`: after `K ≥ 1` steps with `P + 2 ≤ 2^(K+2)`, `nwQQ = ⌊2^(P+1)·ma / mb⌋` and `nwRnz ↔ 2^(P+1)·ma mod mb ≠ 0`
(only `ma < 2^P` is needed of `ma`).
`newton_rest` states it against restoring division (`restQuo`, `restRem` of `P + 2` steps), and `nwNI_spec` shows
that `K = $clog2((P + 9) / 8) + 1` qualifies.

The error analysis is in units of `A = 2^(P-1)`: `S = 2^F·A = 32·A²` is `1` at the scale of `d·r`, so `E = S - mb·r` is
the error `1 - d·r` scaled by `S`, and `2^F = 32·A`, `2^(F+1) = 64·A`, `2^(P+F) = 2·S`, `2^(P+2) = 8·A`.

* `nw_step`: one step with `D = mb·r < 2·S` satisfies `S·(S - mb·r') = (S - D)² + D·(A - D mod A) + A·mb·t` (`t` the
  truncated low part of `r·u`), so the new error is nonnegative and at most `E²/S + (D + 2·S)·A/S`.
* `nw_base`: `|E₀| ≤ S/16` (the linear approximation is within `1/16` on `[1, 2]`).
* `nw_iter_inv`: for `k ≥ 1`, `0 ≤ E_k` and `T·E_k ≤ S + 4·A·T` with `T = 2^(2^(k+2))`, i.e.
  `e_k ≤ 2^-(2^(k+2)) + 2^-(P+2)`; `T` is squared by a step and kept symbolic.
* `nw_quot`: with `E ≤ 8·A` (`e ≤ 2^-(P+1)`), `qf ≤ ⌊2^(P+1)·ma / mb⌋ ≤ qf + 2`; `nw_correct`: the correction.

Plain Lean (Init only, and `Sv.clog2` for the step count): proved by `omega`, `grind` and core lemmas.
-/

namespace LeanModels.Sv.Lib

/-! ## The core, as the hardware computes it -/

/-- `r[0] = 45/32 - 15/32·d` at `F = P + 4` fraction bits. -/
def nwR0 (P mb : Nat) : Nat := 45 * 2 ^ (P - 1) - 15 * mb

/-- `u = ~dr[P+F-1:P-1]`, `dr = mb·r` at `P + F` bits: `2 - d·r` rounded down to `F` fraction bits. -/
def nwU (P mb r : Nat) : Nat := 2 ^ (P + 5) - 1 - mb * r % 2 ^ (2 * P + 4) / 2 ^ (P - 1) % 2 ^ (P + 5)

/-- `r' = ru[2F:F]`, `ru = r·u` at `2F + 1` bits. -/
def nwStep (P mb r : Nat) : Nat := r * nwU P mb r % 2 ^ (2 * P + 9) / 2 ^ (P + 4) % 2 ^ (P + 5)

/-- `r[k]`: `k` Newton steps from `r[0]`. -/
def nwIter (P mb : Nat) : Nat → Nat
  | 0 => nwR0 P mb
  | k + 1 => nwStep P mb (nwIter P mb k)

/-- `qf = qp[P+F-1:F-2]`, `qp = ma·r[K]` at `P + F` bits. -/
def nwQf (P K ma mb : Nat) : Nat := ma * nwIter P mb K % 2 ^ (2 * P + 4) / 2 ^ (P + 2) % 2 ^ (P + 2)

/-- `rm = {ma[0], 0^(P+1)} - qb`, `qb = qf·mb` at `P + 2` bits. -/
def nwRm (P K ma mb : Nat) : Nat :=
  (ma % 2 * 2 ^ (P + 1) + (2 ^ (P + 2) - nwQf P K ma mb * mb % 2 ^ (P + 2))) % 2 ^ (P + 2)

/-- `qq = qf + (rm >= mb) + (rm >= {mb, 1'b0})` at `P + 2` bits. -/
def nwQQ (P K ma mb : Nat) : Nat :=
  (nwQf P K ma mb + (if mb ≤ nwRm P K ma mb then 1 else 0) + (if 2 * mb ≤ nwRm P K ma mb then 1 else 0)) %
    2 ^ (P + 2)

/-- `rnz = (rm != mb) & (rm != {mb, 1'b0}) & (|rm)`. -/
def nwRnz (P K ma mb : Nat) : Prop := nwRm P K ma mb ≠ mb ∧ nwRm P K ma mb ≠ 2 * mb ∧ nwRm P K ma mb ≠ 0

instance (P K ma mb : Nat) : Decidable (nwRnz P K ma mb) := by unfold nwRnz; infer_instance

/-- `r[0]` as the hardware computes it, `45·2^(P-1) - 16·mb + mb` at the context width `F + 1 = P + 5`. -/
theorem nwR0_hw (P mb : Nat) (hP : 1 ≤ P) (hm1 : 2 ^ (P - 1) ≤ mb) (hm2 : mb < 2 ^ P) :
    ((2 ^ (P - 1) * 45 + (2 ^ (P + 5) - 16 * mb)) % 2 ^ (P + 5) + mb) % 2 ^ (P + 5) = nwR0 P mb := by
  obtain ⟨n, rfl⟩ : ∃ n, P = n + 1 := ⟨P - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hm1 ⊢
  have h5 : 2 ^ (n + 1 + 5) = 64 * 2 ^ n := by rw [show n + 1 + 5 = n + 6 by omega, Nat.pow_add]; omega
  have h1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
  rw [h1] at hm2
  unfold nwR0
  rw [Nat.add_sub_cancel, h5]
  have e1 : (2 ^ n * 45 + (64 * 2 ^ n - 16 * mb)) % (64 * 2 ^ n) = 45 * 2 ^ n - 16 * mb := by
    rw [show 2 ^ n * 45 + (64 * 2 ^ n - 16 * mb) = (45 * 2 ^ n - 16 * mb) + 64 * 2 ^ n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : 45 * 2 ^ n - 16 * mb < 64 * 2 ^ n)]
  rw [e1, Nat.mod_eq_of_lt (by omega : 45 * 2 ^ n - 16 * mb + mb < 64 * 2 ^ n)]
  omega

/-! ## Arithmetic -/

/-- The widths of the core in units of `A = 2^(P-1)`. -/
theorem nw_pows (P : Nat) (hP : 1 ≤ P) :
    2 ^ P = 2 * 2 ^ (P - 1) ∧ 2 ^ (P + 1) = 4 * 2 ^ (P - 1) ∧ 2 ^ (P + 2) = 8 * 2 ^ (P - 1) ∧
      2 ^ (P + 4) = 32 * 2 ^ (P - 1) ∧ 2 ^ (P + 5) = 64 * 2 ^ (P - 1) ∧
      2 ^ (2 * P + 4) = 64 * (2 ^ (P - 1) * 2 ^ (P - 1)) ∧
      2 ^ (2 * P + 9) = 2048 * (2 ^ (P - 1) * 2 ^ (P - 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, P = n + 1 := ⟨P - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have e : ∀ c, 2 ^ (n + c) = 2 ^ n * 2 ^ c := fun c => Nat.pow_add 2 n c
  have e2 : ∀ c, 2 ^ (n + n + c) = 2 ^ n * 2 ^ n * 2 ^ c := fun c => by rw [Nat.pow_add, Nat.pow_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e 1]; omega
  · rw [show n + 1 + 1 = n + 2 by omega, e 2]; omega
  · rw [show n + 1 + 2 = n + 3 by omega, e 3]; omega
  · rw [show n + 1 + 4 = n + 5 by omega, e 5]; omega
  · rw [show n + 1 + 5 = n + 6 by omega, e 6]; omega
  · rw [show 2 * (n + 1) + 4 = n + n + 6 by omega, e2 6]; omega
  · rw [show 2 * (n + 1) + 9 = n + n + 11 by omega, e2 11]; omega

/-- `2·a·b ≤ a² + b²`. -/
theorem two_mul_le_add_sq (a b : Nat) : 2 * a * b ≤ a * a + b * b := by
  rcases Nat.le_total a b with h | h
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    have := Nat.zero_le (c * c)
    grind
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    have := Nat.zero_le (c * c)
    grind

/-- A difference `N - y` known to lie in `[0, M)`, computed modulo `M` from `N mod M` and `y mod M`. -/
theorem mod_sub_of_lt (M N y r : Nat) (hM : 0 < M) (h : N = y + r) (hr : r < M) :
    (N % M + (M - y % M)) % M = r := by
  have h2 := Nat.mod_lt y hM
  have h3 : N % M = (y % M + r) % M := by rw [h, Nat.add_mod, Nat.mod_eq_of_lt hr]
  rw [h3]
  generalize y % M = m at *
  by_cases hc : m + r < M
  · rw [Nat.mod_eq_of_lt hc, show m + r + (M - m) = r + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
  · have e : (m + r) % M = m + r - M := by
      rw [Nat.mod_eq_sub_mod (by omega : M ≤ m + r), Nat.mod_eq_of_lt (by omega : m + r - M < M)]
    rw [e, Nat.mod_eq_of_lt (by omega : m + r - M + (M - m) < M)]
    omega

/-! ## One step -/

/-- **One Newton step**, in units of `A`: from `D = mb·r < 2·S`, the product `r·u` stays below `2^(2F)`, the new
reciprocal `r'` satisfies `mb·r' ≤ S` (the error is nonnegative), and the new error `S - mb·r'` is at most
`((S - D)² + A·D + 2·A·S) / S`, stated without subtraction. -/
theorem nw_step (A S mb R : Nat) (hA : 0 < A) (hS : S = 32 * (A * A)) (hm1 : A ≤ mb) (hm2 : mb < 2 * A)
    (hD : mb * R < 2 * S) :
    R * (64 * A - 1 - mb * R / A) < 1024 * (A * A) ∧
      mb * (R * (64 * A - 1 - mb * R / A) / (32 * A)) ≤ S ∧
      S * (S - mb * (R * (64 * A - 1 - mb * R / A) / (32 * A))) + 2 * S * (mb * R) ≤
        S * S + mb * R * (mb * R) + A * (mb * R) + 2 * A * S := by
  have hq := Nat.div_add_mod (mb * R) A
  have hs := Nat.mod_lt (mb * R) hA
  have hqlt : mb * R / A < 64 * A := by
    rw [Nat.div_lt_iff_lt_mul hA]
    have : 2 * S = 64 * A * A := by rw [hS]; grind
    omega
  generalize mb * R / A = q at *
  generalize mb * R % A = s at *
  generalize hu : 64 * A - 1 - q = u
  have hu' : u + q + 1 = 64 * A := by omega
  have hB : 0 < 32 * A := by omega
  have ht := Nat.div_add_mod (R * u) (32 * A)
  have htl := Nat.mod_lt (R * u) hB
  generalize R * u / (32 * A) = R' at *
  generalize R * u % (32 * A) = t at *
  generalize hD' : mb * R = D at *
  obtain ⟨a, ha⟩ : ∃ a, a + s = A := ⟨A - s, by omega⟩
  -- the error identity `S·(S - mb·r') = (S - D)² + D·(A - s) + A·mb·t`, without subtraction
  have hid : S * (mb * R') + D * D + D * a + A * mb * t = 2 * S * D := by
    clear hu hqlt hs htl hD hm1 hm2
    subst hS hD'
    grind
  have hsq := two_mul_le_add_sq S D
  have hSpos : 0 < S := by rw [hS]; exact Nat.mul_pos (by omega) (Nat.mul_pos hA hA)
  -- `r·u < 2^(2F)`: `A·mb·(r·u) = D·(A·u) ≤ D·(2·S - D - 1) ≤ S² - D`
  have hRu : R * u < 1024 * (A * A) := by
    refine Nat.lt_of_not_le fun hc => ?_
    have hAu : A * u + D + 1 ≤ 2 * S := by
      have : A * u + A * q + A = 64 * (A * A) := by
        clear hu hqlt
        grind
      omega
    have h1 : A * A * (1024 * (A * A)) ≤ A * mb * (R * u) := Nat.mul_le_mul (Nat.mul_le_mul_left A hm1) hc
    have h2 : D * (A * u + D + 1) ≤ D * (2 * S) := Nat.mul_le_mul_left D hAu
    have hD0 : D = 0 := by
      clear hid hu hqlt
      subst hS hD'
      have := Nat.zero_le (mb * R)
      grind
    rw [← hD'] at hD0
    rcases Nat.mul_eq_zero.1 hD0 with h | h
    · omega
    · subst h
      rw [Nat.zero_mul] at hc
      have : 0 < 1024 * (A * A) := Nat.mul_pos (by omega) (Nat.mul_pos hA hA)
      omega
  have hle : mb * R' ≤ S := by
    have : S * (mb * R') ≤ S * S := by
      have := Nat.zero_le (D * a)
      have := Nat.zero_le (A * mb * t)
      clear hu hqlt hRu
      grind
    exact Nat.le_of_mul_le_mul_left this hSpos
  refine ⟨hRu, hle, ?_⟩
  obtain ⟨E', hE'⟩ : ∃ E', S = mb * R' + E' := ⟨S - mb * R', by omega⟩
  rw [show S - mb * R' = E' by omega]
  have h1 : D * a ≤ A * D := by rw [Nat.mul_comm A D]; exact Nat.mul_le_mul_left D (by omega)
  have h2 : A * (mb * t) ≤ A * (2 * S) := by
    apply Nat.mul_le_mul_left
    have : mb * t ≤ 2 * A * (32 * A) := Nat.mul_le_mul (by omega) (by omega)
    rw [hS]
    grind
  have h3 : S * S = S * (mb * R') + S * E' := by rw [← Nat.mul_add, ← hE']
  clear hu hqlt hRu hE' hsq
  grind

/-- `nwU` and `nwStep` at `P`: no window wraps when `D = mb·r < 2·S`, and the step is `nw_step`'s. -/
theorem nwStep_spec (P A S mb R : Nat) (hP : 1 ≤ P) (hA : A = 2 ^ (P - 1)) (hS : S = 32 * (A * A))
    (hm1 : A ≤ mb) (hm2 : mb < 2 * A) (hD : mb * R < 2 * S) :
    mb * nwStep P mb R ≤ S ∧
      S * (S - mb * nwStep P mb R) + 2 * S * (mb * R) ≤ S * S + mb * R * (mb * R) + A * (mb * R) + 2 * A * S := by
  obtain ⟨-, -, -, hp4, hp5, hpf, hp2f⟩ := nw_pows P hP
  rw [← hA] at hp4 hp5 hpf hp2f
  have hApos : 0 < A := by rw [hA]; exact Nat.two_pow_pos _
  obtain ⟨hRu, hle, hup⟩ := nw_step A S mb R hApos hS hm1 hm2 hD
  have hD2 : mb * R < 64 * (A * A) := by rw [hS] at hD; omega
  have hq : mb * R / A < 64 * A := by
    rw [Nat.div_lt_iff_lt_mul hApos]
    have : 64 * (A * A) = 64 * A * A := by rw [Nat.mul_assoc]
    omega
  have hU : nwU P mb R = 64 * A - 1 - mb * R / A := by
    unfold nwU
    rw [← hA, hp5, hpf, Nat.mod_eq_of_lt hD2, Nat.mod_eq_of_lt hq]
  generalize 64 * A - 1 - mb * R / A = u at *
  have hRu' : R * u < 2048 * (A * A) := by omega
  have hRu2 : R * u / (32 * A) < 64 * A := by
    rw [Nat.div_lt_iff_lt_mul (show 0 < 32 * A by omega)]
    have : 64 * A * (32 * A) = 2048 * (A * A) := by grind
    omega
  have hStep : nwStep P mb R = R * u / (32 * A) := by
    unfold nwStep
    rw [hU, hp2f, hp4, hp5, Nat.mod_eq_of_lt hRu', Nat.mod_eq_of_lt hRu2]
  rw [hStep]
  exact ⟨hle, hup⟩

/-! ## The error bounds -/

/-- **The initial reciprocal**: `15·S ≤ 16·mb·r₀ ≤ 17·S`, i.e. `|E₀| ≤ S/16`. -/
theorem nw_base (A S mb : Nat) (hS : S = 32 * (A * A)) (hm1 : A ≤ mb) (hm2 : mb < 2 * A) :
    15 * S ≤ 16 * (mb * (45 * A - 15 * mb)) ∧ 16 * (mb * (45 * A - 15 * mb)) ≤ 17 * S := by
  obtain ⟨R, hR⟩ : ∃ R, R + 15 * mb = 45 * A := ⟨45 * A - 15 * mb, by omega⟩
  rw [show 45 * A - 15 * mb = R by omega]
  have hmR : mb * R + 15 * (mb * mb) = 45 * (A * mb) := by grind
  subst hS
  constructor
  · -- `3·A·mb - 2·A² - mb² = c·(A - c)` with `mb = A + c`
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hm1
    have : c * c ≤ A * c := Nat.mul_le_mul_right c (by omega)
    grind
  · -- `60·(15·mb² - 45·A·mb + 34·A²) = (30·mb - 45·A)² + 15·A²`
    have := two_mul_le_add_sq (30 * mb) (45 * A)
    have := Nat.zero_le (A * A)
    grind

/-- The new error from `nw_step`'s bound, with `e = |S - D|`. -/
theorem nw_err_sq (A S D E' e : Nat) (he : S = D + e ∨ D = S + e)
    (hup : S * E' + 2 * S * D ≤ S * S + D * D + A * D + 2 * A * S) : S * E' ≤ e * e + A * D + 2 * A * S := by
  rcases he with rfl | rfl <;> grind

/-- **The first step**: from `|E₀| ≤ S/16`, `256·E₁ ≤ S + 1024·A` (`e₁ ≤ 2^-8 + 2^-(P+2)`). -/
theorem nw_first (A S D E' : Nat) (hSpos : 0 < S) (h15 : 15 * S ≤ 16 * D) (h17 : 16 * D ≤ 17 * S)
    (hup : S * E' + 2 * S * D ≤ S * S + D * D + A * D + 2 * A * S) : 256 * E' ≤ S + 1024 * A := by
  have hA17 : A * (16 * D) ≤ A * (17 * S) := Nat.mul_le_mul_left A h17
  have key : ∃ e, (S = D + e ∨ D = S + e) ∧ 16 * e ≤ S := by
    rcases Nat.le_total D S with h | h
    · exact ⟨S - D, Or.inl (by omega), by omega⟩
    · exact ⟨D - S, Or.inr (by omega), by omega⟩
  obtain ⟨e, he, he16⟩ := key
  have h1 := nw_err_sq A S D E' e he hup
  have h2 : 16 * e * (16 * e) ≤ S * S := Nat.mul_le_mul he16 he16
  have h0 := Nat.zero_le (A * S)
  have : S * (256 * E') ≤ S * (S + 1024 * A) := by grind
  exact Nat.le_of_mul_le_mul_left this hSpos

/-- **A later step**: from `0 ≤ E` and `T·E ≤ S + 4·A·T` (`T ≥ 16`), `T²·E' ≤ S + 4·A·T²`. -/
theorem nw_next (A S T D E' : Nat) (hA : 0 < A) (hS : S = 32 * (A * A)) (hT : 16 ≤ T) (hD : D ≤ S)
    (hinv : T * (S - D) ≤ S + 4 * A * T)
    (hup : S * E' + 2 * S * D ≤ S * S + D * D + A * D + 2 * A * S) : T * T * E' ≤ S + 4 * A * (T * T) := by
  obtain ⟨e, he⟩ : ∃ e, S = D + e := ⟨S - D, by omega⟩
  have h1 := nw_err_sq A S D E' e (Or.inl he) hup
  rw [show S - D = e by omega] at hinv
  have hAD : A * D ≤ A * S := Nat.mul_le_mul_left A hD
  have hSpos : 0 < S := by rw [hS]; exact Nat.mul_pos (by omega) (Nat.mul_pos hA hA)
  have h2 : T * T * (S * E') ≤ T * T * (e * e + 3 * A * S) := Nat.mul_le_mul_left _ (by grind)
  have h3 : T * e * (T * e) ≤ (S + 4 * A * T) * (S + 4 * A * T) := Nat.mul_le_mul hinv hinv
  have h4 : 16 * (A * A * A * T) ≤ T * (A * A * A * T) := Nat.mul_le_mul_right _ hT
  have h5 : 1 * (A * A * T * T) ≤ A * (A * A * T * T) := Nat.mul_le_mul_right _ hA
  have : S * (T * T * E') ≤ S * (S + 4 * A * (T * T)) := by
    clear he h1 hinv hAD hup hD
    subst hS
    grind
  exact Nat.le_of_mul_le_mul_left this hSpos

/-- **The iteration**: for `k ≥ 1`, `mb·r_k ≤ S` and `T·(S - mb·r_k) ≤ S + 4·A·T`, `T = 2^(2^(k+2))`. -/
theorem nw_iter_inv (P A S mb : Nat) (hP : 1 ≤ P) (hA : A = 2 ^ (P - 1)) (hS : S = 32 * (A * A)) (hm1 : A ≤ mb)
    (hm2 : mb < 2 * A) :
    ∀ k, 1 ≤ k → mb * nwIter P mb k ≤ S ∧
      2 ^ 2 ^ (k + 2) * (S - mb * nwIter P mb k) ≤ S + 4 * A * 2 ^ 2 ^ (k + 2) := by
  have hApos : 0 < A := by rw [hA]; exact Nat.two_pow_pos _
  have hSpos : 0 < S := by rw [hS]; exact Nat.mul_pos (by omega) (Nat.mul_pos hApos hApos)
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    show mb * nwStep P mb (nwIter P mb k) ≤ S ∧
      2 ^ 2 ^ (k + 1 + 2) * (S - mb * nwStep P mb (nwIter P mb k)) ≤ S + 4 * A * 2 ^ 2 ^ (k + 1 + 2)
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · -- the first step, from `r₀`
      obtain ⟨h15, h17⟩ := nw_base A S mb hS hm1 hm2
      have hR0 : nwIter P mb 0 = 45 * A - 15 * mb := by rw [hA]; rfl
      rw [← hR0] at h15 h17
      obtain ⟨hle, hup⟩ := nwStep_spec P A S mb (nwIter P mb 0) hP hA hS hm1 hm2 (by omega)
      have h1 := nw_first A S _ _ hSpos h15 h17 hup
      have hT : 2 ^ 2 ^ (0 + 1 + 2) = 256 := by decide
      rw [hT]
      exact ⟨hle, by omega⟩
    · obtain ⟨hle0, hinv0⟩ := ih hk1
      obtain ⟨hle, hup⟩ := nwStep_spec P A S mb (nwIter P mb k) hP hA hS hm1 hm2 (by omega)
      have hT : 16 ≤ 2 ^ 2 ^ (k + 2) := by
        have : 4 ≤ 2 ^ (k + 2) := by
          rw [Nat.pow_add]
          have := Nat.two_pow_pos k
          omega
        calc 16 = 2 ^ 4 := by decide
          _ ≤ 2 ^ 2 ^ (k + 2) := Nat.pow_le_pow_right (by omega) this
      have hTT : 2 ^ 2 ^ (k + 1 + 2) = 2 ^ 2 ^ (k + 2) * 2 ^ 2 ^ (k + 2) := by
        have e : 2 ^ (k + 1 + 2) = 2 ^ (k + 2) + 2 ^ (k + 2) := by
          rw [show k + 1 + 2 = (k + 2) + 1 by omega, Nat.pow_add 2 (k + 2) 1]
          omega
        rw [e, Nat.pow_add]
      have h1 := nw_next A S _ _ _ hApos hS hT hle0 hinv0 hup
      rw [hTT]
      exact ⟨hle, h1⟩

/-! ## The quotient and the correction -/

/-- **The estimate**: with `mb·r ≤ S` and `S - mb·r ≤ 8·A` (`0 ≤ e ≤ 2^-(P+1)`), `qf = ⌊ma·r / 2^(P+2)⌋` satisfies
`qf·mb ≤ 2^(P+1)·ma < (qf + 3)·mb`, and `ma·r` fits its `P + F` bits. -/
theorem nw_quot (A S ma mb R : Nat) (hA : 0 < A) (hS : S = 32 * (A * A)) (ha2 : ma < 2 * A) (hab : ma < 2 * mb)
    (hb1 : A ≤ mb) (hD : mb * R ≤ S) (hE : S - mb * R ≤ 8 * A) :
    ma * R < 64 * (A * A) ∧ ma * R / (8 * A) * mb ≤ 4 * A * ma ∧ 4 * A * ma < (ma * R / (8 * A) + 3) * mb := by
  have hR : R ≤ 32 * A := by
    have : A * R ≤ A * (32 * A) := by
      have := Nat.mul_le_mul_right R hb1
      grind
    exact Nat.le_of_mul_le_mul_left this hA
  have hX : ma * R < 64 * (A * A) := by
    have h1 : ma * R ≤ ma * (32 * A) := Nat.mul_le_mul_left ma hR
    have h2 : ma * (32 * A) < 2 * A * (32 * A) := Nat.mul_lt_mul_of_pos_right ha2 (by omega)
    grind
  refine ⟨hX, ?_, ?_⟩
  · have hx := Nat.div_add_mod (ma * R) (8 * A)
    generalize ma * R / (8 * A) = qf at *
    generalize ma * R % (8 * A) = x0 at *
    have h1 : ma * (mb * R) ≤ ma * S := Nat.mul_le_mul_left ma hD
    have h2 : mb * (ma * R) = mb * (8 * A * qf + x0) := by rw [hx]
    have h0 : 0 ≤ mb * x0 := Nat.zero_le _
    have : 8 * A * (qf * mb) ≤ 8 * A * (4 * A * ma) := by
      subst hS
      grind
    exact Nat.le_of_mul_le_mul_left this (by omega)
  · have hx := Nat.div_add_mod (ma * R) (8 * A)
    have hxl := Nat.mod_lt (ma * R) (show 0 < 8 * A by omega)
    generalize ma * R / (8 * A) = qf at *
    generalize ma * R % (8 * A) = x0 at *
    obtain ⟨E, hE'⟩ : ∃ E, S = mb * R + E := ⟨S - mb * R, by omega⟩
    have hE8 : E ≤ 8 * A := by omega
    have h1 : ma * S = ma * (mb * R + E) := by rw [← hE']
    have h2 : mb * (ma * R) = mb * (8 * A * qf + x0) := by rw [hx]
    have h3 : ma * E ≤ ma * (8 * A) := Nat.mul_le_mul_left ma hE8
    have h4 : (ma + 1) * (8 * A) ≤ 2 * mb * (8 * A) := Nat.mul_le_mul_right _ (by omega)
    have h5 : mb * (x0 + 1) ≤ mb * (8 * A) := Nat.mul_le_mul_left mb (by omega)
    have : 8 * A * (4 * A * ma) < 8 * A * ((qf + 3) * mb) := by
      subst hS
      grind
    exact Nat.lt_of_mul_lt_mul_left this

/-- **The correction**: with `N = qf·mb + rm` and `rm < 3·mb`, `qf + [rm ≥ mb] + [rm ≥ 2·mb] = ⌊N / mb⌋` and the
remainder is zero iff `rm ∈ {0, mb, 2·mb}`. -/
theorem nw_correct (N mb qf rm M : Nat) (hmb : 0 < mb) (h : N = qf * mb + rm) (hrm : rm < 3 * mb)
    (hM : N / mb < M) :
    (qf + (if mb ≤ rm then 1 else 0) + (if 2 * mb ≤ rm then 1 else 0)) % M = N / mb ∧
      ((rm ≠ mb ∧ rm ≠ 2 * mb ∧ rm ≠ 0) ↔ N % mb ≠ 0) := by
  have hl := Nat.mod_lt rm hmb
  rcases mod3 rm mb hmb hrm with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · obtain ⟨hq, hr⟩ := divmod_unique mb qf (rm % mb) N hmb hl (by rw [h, h1])
    rw [hq] at hM ⊢
    have n1 : ¬ mb ≤ rm := by omega
    have n2 : ¬ 2 * mb ≤ rm := by omega
    rw [hr, h1, if_neg n1, if_neg n2, Nat.mod_eq_of_lt (by omega : qf + 0 + 0 < M)]
    exact ⟨rfl, fun hh => hh.2.2, fun hh => ⟨by omega, by omega, hh⟩⟩
  · obtain ⟨hq, hr⟩ := divmod_unique mb (qf + 1) (rm % mb) N hmb hl (by rw [h, Nat.add_mul]; omega)
    rw [hq] at hM ⊢
    have n2 : ¬ 2 * mb ≤ rm := by omega
    rw [hr, if_pos h2, if_neg n2, Nat.mod_eq_of_lt (by omega : qf + 1 + 0 < M)]
    generalize rm % mb = r at *
    exact ⟨rfl, fun hh => by omega, fun hh => ⟨by omega, by omega, by omega⟩⟩
  · obtain ⟨hq, hr⟩ := divmod_unique mb (qf + 2) (rm % mb) N hmb hl (by rw [h, Nat.add_mul]; omega)
    rw [hq] at hM ⊢
    have p1 : mb ≤ rm := by omega
    rw [hr, if_pos p1, if_pos h2, Nat.mod_eq_of_lt (by omega : qf + 1 + 1 < M)]
    generalize rm % mb = r at *
    exact ⟨rfl, fun hh => by omega, fun hh => ⟨by omega, by omega, by omega⟩⟩

/-! ## The divider -/

/-- **Newton-Raphson division.** For `mb ∈ [2^(P-1), 2^P)`, `ma < 2^P` and `K ≥ 1` steps with
`P + 2 ≤ 2^(K+2)`, the core's quotient is `⌊2^(P+1)·ma / mb⌋` and its sticky is the remainder test. -/
theorem newton_div (P K ma mb : Nat) (hP : 2 ≤ P) (ha : ma < 2 ^ P)
    (hb1 : 2 ^ (P - 1) ≤ mb) (hb2 : mb < 2 ^ P) (hK : 1 ≤ K) (hKP : P + 2 ≤ 2 ^ (K + 2)) :
    nwQQ P K ma mb = 2 ^ (P + 1) * ma / mb ∧ (nwRnz P K ma mb ↔ 2 ^ (P + 1) * ma % mb ≠ 0) := by
  obtain ⟨hp0, hp1, hp2, -, -, hpf, -⟩ := nw_pows P (by omega)
  have hT : 2 ^ (P + 2) ≤ 2 ^ 2 ^ (K + 2) := Nat.pow_le_pow_right (by omega) hKP
  generalize hA : 2 ^ (P - 1) = A at *
  have hApos : 0 < A := by rw [← hA]; exact Nat.two_pow_pos _
  have hab : ma < 2 * mb := by omega
  obtain ⟨hle, hinv⟩ := nw_iter_inv P A (32 * (A * A)) mb (by omega) hA.symm rfl hb1 (by omega) K hK
  -- the final error: `T·E ≤ S + 4·A·T` with `S = 4·A·(8·A) ≤ 4·A·T` gives `E ≤ 8·A`
  have hE : 32 * (A * A) - mb * nwIter P mb K ≤ 8 * A := by
    generalize 2 ^ 2 ^ (K + 2) = T at *
    generalize 32 * (A * A) - mb * nwIter P mb K = E at *
    have h1 : 4 * A * (8 * A) ≤ 4 * A * T := Nat.mul_le_mul_left _ (by omega)
    have h2 : T * E ≤ T * (8 * A) := by grind
    exact Nat.le_of_mul_le_mul_left h2 (by omega)
  generalize hR : nwIter P mb K = R at *
  obtain ⟨hX, hlo, hhi⟩ := nw_quot A (32 * (A * A)) ma mb R hApos rfl (by omega) hab hb1 hle hE
  have hqf : nwQf P K ma mb = ma * R / (8 * A) := by
    unfold nwQf
    have hq8 : ma * R / (8 * A) < 8 * A := by
      rw [Nat.div_lt_iff_lt_mul (show 0 < 8 * A by omega)]
      have : 8 * A * (8 * A) = 64 * (A * A) := by grind
      omega
    rw [hR, hpf, hp2, Nat.mod_eq_of_lt hX, Nat.mod_eq_of_lt hq8]
  generalize ma * R / (8 * A) = qf at *
  have hN8 : 4 * A * ma % (8 * A) = ma % 2 * (4 * A) := by
    rw [show 8 * A = 4 * A * 2 by omega, Nat.mul_mod_mul_left]
    exact Nat.mul_comm _ _
  have hhi' : 4 * A * ma < qf * mb + 3 * mb := by rw [Nat.add_mul] at hhi; exact hhi
  have hrm : nwRm P K ma mb = 4 * A * ma - qf * mb := by
    unfold nwRm
    rw [hqf, hp1, hp2, ← hN8]
    exact mod_sub_of_lt (8 * A) (4 * A * ma) (qf * mb) _ (by omega) (by omega) (by omega)
  have hQ : 4 * A * ma / mb < 8 * A := by
    rw [Nat.div_lt_iff_lt_mul (show 0 < mb by omega)]
    have : 4 * A * ma < 4 * A * (2 * mb) := Nat.mul_lt_mul_of_pos_left hab (by omega)
    grind
  obtain ⟨h1, h2⟩ := nw_correct (4 * A * ma) mb qf (4 * A * ma - qf * mb) (8 * A) (by omega) (by omega)
    (by omega) hQ
  unfold nwQQ nwRnz
  rw [hrm, hqf, hp2, hp1]
  exact ⟨h1, h2⟩

/-- `newton_div` against restoring division: the quotient and the sticky of `P + 2` restoring steps. -/
theorem newton_rest (P K ma mb : Nat) (hP : 2 ≤ P) (ha : ma < 2 ^ P)
    (hb1 : 2 ^ (P - 1) ≤ mb) (hb2 : mb < 2 ^ P) (hK : 1 ≤ K) (hKP : P + 2 ≤ 2 ^ (K + 2)) :
    nwQQ P K ma mb = restQuo mb ma (P + 2) ∧ (nwRnz P K ma mb ↔ restRem mb ma (P + 2) ≠ 0) := by
  obtain ⟨hp0, -⟩ := nw_pows P (by omega)
  have := Nat.two_pow_pos (P - 1)
  obtain ⟨h1, h2⟩ := newton_div P K ma mb hP ha hb1 hb2 hK hKP
  obtain ⟨e1, e2⟩ := restore_spec mb ma (P + 1) (by omega) (by omega)
  rw [show P + 1 + 1 = P + 2 from rfl] at e1 e2
  rw [e1, e2, h1, h2]
  generalize 2 ^ (P + 1) * ma % mb = r
  exact ⟨rfl, fun h => by omega, fun h => by omega⟩

/-- **The step count** `NI = $clog2((P + 9) / 8) + 1`: `1 ≤ NI` and `P + 2 ≤ 2^(NI+2)`. -/
theorem nwNI_spec (P : Nat) : 1 ≤ clog2 ((P + 9) / 8) + 1 ∧ P + 2 ≤ 2 ^ (clog2 ((P + 9) / 8) + 1 + 2) := by
  refine ⟨by omega, ?_⟩
  unfold clog2
  split
  · show P + 2 ≤ 8
    omega
  · have hl := Nat.lt_log2_self (n := (P + 9) / 8 - 1)
    generalize ((P + 9) / 8 - 1).log2 = L at hl ⊢
    rw [show L + 1 + 1 + 2 = (L + 1) + 3 by omega, Nat.pow_add]
    generalize 2 ^ (L + 1) = M at hl ⊢
    show P + 2 ≤ M * 8
    omega

/-- `newton_div` and `newton_rest` at `NI = $clog2((P + 9) / 8) + 1` steps. -/
theorem newton_NI (P ma mb : Nat) (hP : 2 ≤ P) (ha : ma < 2 ^ P)
    (hb1 : 2 ^ (P - 1) ≤ mb) (hb2 : mb < 2 ^ P) :
    nwQQ P (clog2 ((P + 9) / 8) + 1) ma mb = restQuo mb ma (P + 2) ∧
      (nwRnz P (clog2 ((P + 9) / 8) + 1) ma mb ↔ restRem mb ma (P + 2) ≠ 0) :=
  newton_rest P _ ma mb hP ha hb1 hb2 (nwNI_spec P).1 (nwNI_spec P).2

end LeanModels.Sv.Lib
