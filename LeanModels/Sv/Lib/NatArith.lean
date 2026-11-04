/-!
# `LeanModels.Sv.Lib.NatArith`: `Nat` and `Int` arithmetic for word-level proofs (no imports)

Facts about `Nat` (and the `Int` labels of windows) that word-level datapath proofs keep needing and core does not
state in this form:

* `log2_mul_two_pow`: the `log2` of a value shifted left by `j`;
* `mul_pow_mul_pow`, `mul_pow_mul_pow_mul_pow`: a product of powers of one base, collected;
* `scale_le`, `scale_ge`, `scale_lt`, `scale_gt`: a comparison with a fraction `N / D`, scaled to one with
  `T / S` when `N * S = D * T`;
* `add_two_pow_sub_mod_two_pow`: a subtraction modulo `2^M` read modulo `2^w`, `w ≤ M`;
* `add_sub_one_mod_of_lt`: a decrement modulo `Z`;
* `mod_cases_of_lt_three_mul`: the three bands of `x < 3 * Z` and `x % Z` in each;
* `div_mod_two_eq_zero_iff_lt`: the top bit of a value below `2 * H`;
* row-major windows: `mul_add_mem_window_iff`, `rowMajor_window_le`, and the `Int` labels an instantiated part
  select is checked with (`window_bounds_of_natCast`, `min_add_sub_one_self`, `max_add_sub_one_self`,
  `add_sub_one_sub_add_one`, `natAbs_sub_one_add_one`); that row `i` ends before row `i' > i` begins
  (`i·K + K ≤ i'·K`) is `LeanModels.Sv.rowMajor_le` (`Hier2Gen.lean`);
* `two_mul_le_mul_self_add_mul_self`: `2ab ≤ a² + b²`;
* `mod_add_sub_mod_of_eq_add`: a difference known to lie in `[0, M)`, computed modulo `M`.

Plain Lean (Init only): nothing here mentions an SV design. Proved by `omega`, `grind` and core lemmas. Core already
has, and this file does not restate: `Nat.mul_lt_mul_of_pos_left` (`k * x < k * y`), `Nat.div_mod_unique`
(quotient and remainder by uniqueness), `Nat.mod_mul` (a remainder split at a product).
-/

namespace LeanModels.Sv.Lib

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

/-! ## Scaled comparisons: with `N * S = D * T`, `X` against `N / D` is `X` against `T / S` -/

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

/-- With `N * S = D * T`: `N < D * X` (`N / D < X`) exactly when `T < S * X` (`T / S < X`). -/
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

/-! ## Modular facts -/

/-- **A subtraction at a wider width, read at width `w`**: `y + (2^M - c)` (the two's-complement `y - c` at
`M ≥ w` bits, `c ≤ 2^w`) is, modulo `2^w`, `y + (2^w - c)`, the same subtraction at `w` bits. -/
theorem add_two_pow_sub_mod_two_pow (y c w M : Nat) (hc2 : c ≤ 2 ^ w) (hM : w ≤ M) :
    (y + (2 ^ M - c)) % 2 ^ w = (y + (2 ^ w - c)) % 2 ^ w := by
  obtain ⟨m, rfl⟩ : ∃ m, M = w + m := ⟨M - w, by omega⟩
  have h1 : 2 ^ (w + m) = 2 ^ w * 2 ^ m := Nat.pow_add _ _ _
  have h2 : 1 ≤ 2 ^ m := Nat.two_pow_pos m
  have h3 : 2 ^ w * 1 ≤ 2 ^ w * 2 ^ m := Nat.mul_le_mul_left _ h2
  have h4 : 2 ^ w * (2 ^ m - 1) = 2 ^ w * 2 ^ m - 2 ^ w := Nat.mul_sub_one _ _
  have e : y + (2 ^ (w + m) - c) = (y + (2 ^ w - c)) + 2 ^ w * (2 ^ m - 1) := by omega
  rw [e, Nat.add_mul_mod_self_left]

/-- A decrement modulo `Z`: `y - 1`, wrapping `0` to `Z - 1`. -/
theorem add_sub_one_mod_of_lt (Z y : Nat) (hy : y < Z) : (y + (Z - 1)) % Z = if y = 0 then Z - 1 else y - 1 := by
  by_cases h0 : y = 0
  · subst h0
    rw [if_pos rfl, Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [if_neg h0]
    have e : y + (Z - 1) = (y - 1) + Z := by omega
    rw [e, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

/-- The three bands of `x < 3 * Z` and `x % Z` in each. -/
theorem mod_cases_of_lt_three_mul (x Z : Nat) (hx : x < 3 * Z) :
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

/-- **The top bit of a value below `2 * H`**: the quotient bit `x / H % 2` is `0` exactly when `x < H`. -/
theorem div_mod_two_eq_zero_iff_lt (x H : Nat) (hx : x < 2 * H) : (x / H % 2 = 0 ↔ x < H) := by
  have hH : 0 < H := by omega
  by_cases h : x < H
  · have e : x / H = 0 := Nat.div_eq_of_lt h
    rw [e]; simp [h]
  · have h1 : 1 ≤ x / H := (Nat.le_div_iff_mul_le hH).2 (by omega)
    have h2 : x / H < 2 := (Nat.div_lt_iff_lt_mul hH).2 (by omega)
    have e : x / H = 1 := by omega
    rw [e]; simp [h]

/-! ## Row-major windows and their `Int` labels -/

/-- Bit `r·W + j` (`j < W`) lies in the window `[m·W, m·W + W)` exactly when `r = m`. -/
theorem mul_add_mem_window_iff {W r m j : Nat} (hj : j < W) :
    (m * W ≤ r * W + j ∧ r * W + j < m * W + W) ↔ r = m := by
  refine ⟨fun ⟨h1, h2⟩ => ?_, by rintro rfl; omega⟩
  rcases Nat.lt_trichotomy r m with h | h | h
  · have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt h); rw [Nat.succ_mul] at this; omega
  · exact h
  · have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt h); rw [Nat.succ_mul] at this; omega

/-- Entry `(i, j)` of an `M×N` row-major array of `w`-bit entries, at offset `(i·N + j)·w`, ends inside the
array. -/
theorem rowMajor_window_le {M N w i j : Nat} (hi : i < M) (hj : j < N) : (i * N + j) * w + w ≤ M * N * w := by
  have h : i * N + j + 1 ≤ M * N := by
    have := Nat.mul_le_mul_right N (show i + 1 ≤ M by omega); rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have := Nat.mul_le_mul_right w h; rwa [Nat.add_mul, Nat.one_mul] at this

/-- **The `Int` labels of an in-range window** `[x, x + w)` of a `y`-bit vector (`x`, `y` the casts of `lo`, `c`
with `lo + w ≤ c`, `w > 0`): the facts the range checks of an instantiated part select need. -/
theorem window_bounds_of_natCast (x y : Int) {lo w c : Nat} (h : lo + w ≤ c) (hw : 0 < w) (hx : (lo : Int) = x)
    (hy : (c : Int) = y) : 0 ≤ x ∧ x.toNat = lo ∧ x + w - 1 < y ∧ 1 ≤ x + w ∧ (x + w).toNat = lo + w :=
  ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- The low end of a nonempty range `[a + w - 1 : a]`: `min (a + w - 1) a = a`. -/
theorem min_add_sub_one_self (a : Int) {w : Int} (h : 0 < w) : min (a + w - 1) a = a := by omega

/-- The high end of a nonempty range `[a + w - 1 : a]`: `max (a + w - 1) a = a + w - 1`. -/
theorem max_add_sub_one_self (a : Int) {w : Int} (h : 0 < w) : max (a + w - 1) a = a + w - 1 := by omega

/-- The width of the range `[a + w - 1 : a]`: `(a + w - 1) - a + 1 = w`. -/
theorem add_sub_one_sub_add_one (a w : Int) : a + w - 1 - a + 1 = w := by omega

/-- The width of a declared range `[x - 1 : 0]`, `x > 0`: `(x - 1).natAbs + 1 = x`. -/
theorem natAbs_sub_one_add_one {x : Nat} (h : 0 < x) : ((x : Int) - 1).natAbs + 1 = x := by omega

/-! ## Products and remainders -/

/-- `2·a·b ≤ a² + b²` (the square of `a - b` is nonnegative), stated without subtraction. -/
theorem two_mul_le_mul_self_add_mul_self (a b : Nat) : 2 * a * b ≤ a * a + b * b := by
  rcases Nat.le_total a b with h | h
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    have := Nat.zero_le (c * c)
    grind
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    have := Nat.zero_le (c * c)
    grind

/-- A difference `N - y` known to lie in `[0, M)`, computed modulo `M` from `N mod M` and `y mod M`. -/
theorem mod_add_sub_mod_of_eq_add (M N y r : Nat) (h : N = y + r) (hr : r < M) :
    (N % M + (M - y % M)) % M = r := by
  have h2 := Nat.mod_lt y (by omega : 0 < M)
  have h3 : N % M = (y % M + r) % M := by rw [h, Nat.add_mod, Nat.mod_eq_of_lt hr]
  rw [h3]
  generalize y % M = m at *
  by_cases hc : m + r < M
  · rw [Nat.mod_eq_of_lt hc, show m + r + (M - m) = r + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
  · have e : (m + r) % M = m + r - M := by
      rw [Nat.mod_eq_sub_mod (by omega : M ≤ m + r), Nat.mod_eq_of_lt (by omega : m + r - M < M)]
    rw [e, Nat.mod_eq_of_lt (by omega : m + r - M + (M - m) < M)]
    omega

end LeanModels.Sv.Lib
