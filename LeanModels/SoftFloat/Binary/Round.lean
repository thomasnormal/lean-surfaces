import LeanModels.SoftFloat.Binary.Defs
import LeanModels.SoftFloat.Binary.Nat

/-!
# Correct rounding of an exact magnitude (§4.3, §7.4)

Magnitudes are measured in *units* of the least subnormal `2^qmin`, where every finite number of a format is a natural
number and a representable magnitude is `c·2^j` with `c < 2^p` (`RepU`; unbounded exponent range, as §4.3 and §7.4
round). `roundUnits f mode neg N D` rounds the exact magnitude `N / D`; this file proves what that means.

* `gap`: no representable magnitude lies strictly between the two neighbours `c·2^j`, `(c+1)·2^j` of `N / D`;
* roundTiesToEven (§4.3.1): `rne_rep` (the result is representable), `rne_nearest` (nothing representable is
  nearer), `rne_tie_even` (on a tie the significand is even, `EvenSig`), `rne_two_even` (two even neighbours cannot
  both be nearest), and `rne_overflow_iff`, the overflow threshold of §4.3.1/§7.4 in units: the result exceeds the
  largest finite magnitude iff `N / D ≥ maxUnits + half the top spacing`;
* `roundUnits_scale`: only the ratio `N / D` matters, for every attribute;
* `rne_eq_iff`, `rne_eq_iff_canon`: the interval characterization (the result is `u` iff `N / D` is within half a
  spacing of `u`, a boundary only for an even significand), which a certificate checks with `+ - *` alone;
* `IsRoundedTo`: the five attributes of §4.3.1-§4.3.2 stated declaratively over the exact magnitude, and
  `roundUnits_isRoundedTo`: `roundUnits` satisfies it, for every format and attribute.

Ported from svGolf's fdivp reference proof (sections `IEEE754Proofs`, `ScaleInvariance`, `RneInterval`), the
maintainers' text, with the declarative attributes added.
-/

namespace LeanModels.SoftFloat.Binary

open NatFacts

/-- `u` units is a magnitude representable with `p` significand bits and an unbounded
exponent range: `u = c × 2^j` with `c < 2^p`. -/
def RepU (f : Format) (u : Nat) : Prop := ∃ c j, c < 2 ^ f.p ∧ u = c * 2 ^ j

theorem two_pow_pred (f : Format) : 2 ^ f.p = 2 ^ (f.p - 1) * 2 := by
  have := f.hp
  rw [← Nat.pow_succ]; congr 1; omega

/-- The truncated significand `c = ⌊N / (D·2^j)⌋` has at most `p` bits, and exactly `p` bits
when `j > 0`. -/
theorem trunc_bounds (f : Format) (N D : Nat) :
    N / (D * 2 ^ ulpExp f (N / D)) < 2 ^ f.p ∧
    (0 < ulpExp f (N / D) → 2 ^ (f.p - 1) ≤ N / (D * 2 ^ ulpExp f (N / D))) := by
  have hp := f.hp
  rw [← Nat.div_div_eq_div_mul]
  generalize N / D = n
  unfold ulpExp
  constructor
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by omega) (by omega))
  · intro hj
    have hn : n ≠ 0 := by
      rintro rfl
      simp [Nat.log2_zero] at hj
      omega
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.log2_self_le hn)

/-- No representable magnitude lies strictly between `c·2^j` and `(c+1)·2^j`, when `c` has
`p` bits or `j = 0`. -/
theorem gap (f : Format) (c j w : Nat) (hc : 0 < j → 2 ^ (f.p - 1) ≤ c) (hw : RepU f w) :
    w ≤ c * 2 ^ j ∨ (c + 1) * 2 ^ j ≤ w := by
  obtain ⟨c', i, hc', rfl⟩ := hw
  by_cases hij : j ≤ i
  · have e : c' * 2 ^ i = c' * 2 ^ (i - j) * 2 ^ j := by
      rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
    rw [e]
    by_cases h : c' * 2 ^ (i - j) ≤ c
    · exact .inl (Nat.mul_le_mul_right _ h)
    · exact .inr (Nat.mul_le_mul_right _ (by omega))
  · left
    have hj : 0 < j := by omega
    have h1 := hc hj
    have h2 : 2 ^ i * 2 ≤ 2 ^ j := by
      rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by omega) (by omega)
    calc c' * 2 ^ i ≤ 2 ^ f.p * 2 ^ i := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (f.p - 1) * (2 ^ i * 2) := by rw [two_pow_pred]; ac_rfl
      _ ≤ c * 2 ^ j := Nat.mul_le_mul h1 h2

/-- `v`'s significand at its own spacing (`v / 2^ulpExp v`, the integral significand `c` of
§3.3, or the subnormal `T`) is even. -/
def EvenSig (f : Format) (v : Nat) : Prop := v / 2 ^ ulpExp f v % 2 = 0

theorem evenSig_of (f : Format) (e j : Nat) (he : e % 2 = 0) (hle : e ≤ 2 ^ f.p)
    (hn : 0 < j → 2 ^ (f.p - 1) ≤ e) : EvenSig f (e * 2 ^ j) := by
  have hp := f.hp
  unfold EvenSig ulpExp
  rcases Nat.eq_zero_or_pos e with rfl | hpos
  · simp
  rcases Nat.lt_or_eq_of_le hle with hlt | rfl
  · rw [log2_mul_two_pow j (by omega)]
    have hl : e.log2 < f.p := (Nat.log2_lt (by omega)).2 hlt
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have : e.log2 + 0 + 1 - f.p = 0 := by omega
      simp [this, he]
    · have hl2 : f.p - 1 ≤ e.log2 := (Nat.le_log2 (by omega)).2 (hn hj)
      have : e.log2 + j + 1 - f.p = j := by omega
      rw [this, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]; exact he
  · rw [← Nat.pow_add, Nat.log2_two_pow]
    have : f.p + j + 1 - f.p = j + 1 := by omega
    rw [this, Nat.pow_div (by omega) (by omega)]
    have : f.p + j - (j + 1) = (f.p - 2) + 1 := by omega
    rw [this, Nat.pow_succ]; simp

/-- The pieces of `roundUnits`: `N = M·c + r` with `M = D·2^j`, `r < M`. -/
theorem rne_unfold (f : Format) (neg : Bool) (N D : Nat) :
    roundUnits f .nearestTiesToEven neg N D =
      (if 2 * (N % (D * 2 ^ ulpExp f (N / D))) > D * 2 ^ ulpExp f (N / D) ∨
          (2 * (N % (D * 2 ^ ulpExp f (N / D))) = D * 2 ^ ulpExp f (N / D) ∧
           N / (D * 2 ^ ulpExp f (N / D)) % 2 = 1)
        then N / (D * 2 ^ ulpExp f (N / D)) + 1 else N / (D * 2 ^ ulpExp f (N / D)))
        * 2 ^ ulpExp f (N / D) := by
  simp only [roundUnits]
  congr 1
  split <;> split <;> simp_all

/-- **roundTiesToEven delivers a nearest representable magnitude** (§4.3.1): no magnitude
`w = c·2^j` with `c < 2^p` is strictly closer to `N / D` (all exponents allowed). -/
theorem rne_nearest (f : Format) (neg : Bool) (N D : Nat) (hD : 0 < D) (w : Nat)
    (hw : RepU f w) :
    udist N D (roundUnits f .nearestTiesToEven neg N D) ≤ udist N D w := by
  obtain ⟨-, hc2⟩ := trunc_bounds f N D
  rw [rne_unfold]
  generalize ulpExp f (N / D) = j at *
  have hM : 0 < D * 2 ^ j := Nat.mul_pos hD (Nat.two_pow_pos _)
  have hdm := Nat.div_add_mod N (D * 2 ^ j)
  have hr := Nat.mod_lt N hM
  generalize N / (D * 2 ^ j) = c at *
  generalize N % (D * 2 ^ j) = r at *
  have hg := gap f c j w hc2 hw
  have e1 : c * 2 ^ j * D = D * 2 ^ j * c := by ac_rfl
  have e2 : (c + 1) * 2 ^ j * D = D * 2 ^ j * c + D * 2 ^ j := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; ac_rfl
  have hg' : w * D ≤ D * 2 ^ j * c ∨ D * 2 ^ j * c + D * 2 ^ j ≤ w * D := by
    rcases hg with h | h
    · exact .inl (e1 ▸ Nat.mul_le_mul_right D h)
    · exact .inr (e2 ▸ Nat.mul_le_mul_right D h)
  unfold udist
  generalize D * 2 ^ j * c = X at *
  generalize D * 2 ^ j = M at *
  split <;> omega

/-- **Ties go to even** (§4.3.1): if a different representable magnitude is as close to
`N / D` as the roundTiesToEven result, the result's significand is even. -/
theorem rne_tie_even (f : Format) (neg : Bool) (N D : Nat) (hD : 0 < D) (w : Nat)
    (hw : RepU f w) (hne : w ≠ roundUnits f .nearestTiesToEven neg N D)
    (hle : udist N D w ≤ udist N D (roundUnits f .nearestTiesToEven neg N D)) :
    EvenSig f (roundUnits f .nearestTiesToEven neg N D) := by
  obtain ⟨hc1, hc2⟩ := trunc_bounds f N D
  rw [rne_unfold] at *
  generalize ulpExp f (N / D) = j at *
  have hM : 0 < D * 2 ^ j := Nat.mul_pos hD (Nat.two_pow_pos _)
  have hdm := Nat.div_add_mod N (D * 2 ^ j)
  have hr := Nat.mod_lt N hM
  generalize N / (D * 2 ^ j) = c at *
  generalize N % (D * 2 ^ j) = r at *
  have hg := gap f c j w hc2 hw
  have e1 : c * 2 ^ j * D = D * 2 ^ j * c := by ac_rfl
  have e2 : (c + 1) * 2 ^ j * D = D * 2 ^ j * c + D * 2 ^ j := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; ac_rfl
  -- w is one of the two neighbours c·2^j, (c+1)·2^j
  have hw2 : w = c * 2 ^ j ∨ w = (c + 1) * 2 ^ j := by
    rcases hg with h | h
    · rcases Nat.lt_or_eq_of_le h with h | h
      · exfalso
        have := e1 ▸ Nat.mul_le_mul_right D (Nat.succ_le_of_lt h)
        rw [Nat.succ_mul] at this
        unfold udist at hle
        generalize D * 2 ^ j * c = X at *
        generalize D * 2 ^ j = M at *
        split at hle <;> omega
      · exact .inl h
    · rcases Nat.lt_or_eq_of_le h with h | h
      · exfalso
        have := Nat.mul_le_mul_right D (Nat.succ_le_of_lt h)
        rw [Nat.succ_mul, e2] at this
        unfold udist at hle
        generalize D * 2 ^ j * c = X at *
        generalize D * 2 ^ j = M at *
        split at hle <;> omega
      · exact .inr h.symm
  have hcp : c + 1 ≤ 2 ^ f.p := hc1
  split
  · next hup =>
    rcases hw2 with rfl | rfl
    · apply evenSig_of f (c + 1) j _ hcp (fun hj => Nat.le_succ_of_le (hc2 hj))
      have := hle
      rw [if_pos hup] at this
      unfold udist at this
      rw [e1, e2] at this
      generalize D * 2 ^ j * c = X at *
      generalize D * 2 ^ j = M at *
      omega
    · exact absurd rfl (by rwa [if_pos hup] at hne)
  · next hup =>
    rcases hw2 with rfl | rfl
    · exact absurd rfl (by rwa [if_neg hup] at hne)
    · apply evenSig_of f c j _ (by omega) hc2
      have := hle
      rw [if_neg hup] at this
      unfold udist at this
      rw [e1, e2] at this
      generalize D * 2 ^ j * c = X at *
      generalize D * 2 ^ j = M at *
      omega

theorem emax_pos (f : Format) : 1 ≤ f.emax := by
  have := f.hw
  unfold Format.emax
  have : 2 ≤ 2 ^ (f.w - 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (f.w - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem two_emax (f : Format) : 2 * f.emax + 2 = 2 ^ f.w := by
  have := f.hw
  have h2 : 2 * 2 ^ (f.w - 1) = 2 ^ f.w := by
    rw [← Nat.pow_succ']; congr 1; omega
  have := emax_pos f
  unfold Format.emax at *; omega

theorem rep_dvd (f : Format) (u : Nat) (hu : RepU f u) (hu0 : u ≠ 0) :
    2 ^ (Nat.log2 u - f.t) ∣ u := by
  obtain ⟨c, i, hc, rfl⟩ := hu
  have hc0 : c ≠ 0 := by rintro rfl; simp at hu0
  rw [log2_mul_two_pow i hc0]
  have : c.log2 < f.p := (Nat.log2_lt hc0).2 hc
  exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by simp only [Format.t]; omega))
    (Nat.dvd_mul_left _ _)

/-- For `2^t ≤ u ≤ maxUnits`, with `j = ⌊log₂ u⌋ − t`: the significand `u / 2^j` has exactly
`p` bits and the biased exponent `j + 1` is that of a finite number. -/
theorem normal_bounds (f : Format) (u : Nat) (hmax : u ≤ f.maxUnits) (hge : 2 ^ f.t ≤ u) :
    2 ^ f.t ≤ u / 2 ^ (u.log2 - f.t) ∧ u / 2 ^ (u.log2 - f.t) - 2 ^ f.t < 2 ^ f.t ∧
    u.log2 - f.t + 1 < 2 ^ f.w - 1 := by
  have hp := f.hp
  have hw2 := two_emax f
  have hu0 : u ≠ 0 := by have := Nat.two_pow_pos f.t; omega
  have hl : f.t ≤ u.log2 := (Nat.le_log2 hu0).2 hge
  have hlo : 2 ^ f.t ≤ u / 2 ^ (u.log2 - f.t) := by
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.log2_self_le hu0)
  have hhi : u / 2 ^ (u.log2 - f.t) < 2 ^ f.p := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le Nat.lt_log2_self
      (Nat.pow_le_pow_right (by omega) (by simp only [Format.t] at *; omega))
  have ht : 2 ^ f.t + 2 ^ f.t = 2 ^ f.p := by
    rw [← Nat.two_mul, ← Nat.pow_succ']; congr 1; simp only [Format.t]; omega
  refine ⟨hlo, by omega, ?_⟩
  have hm : f.maxUnits < 2 ^ (f.p + (2 * f.emax - 1)) := by
    unfold Format.maxUnits
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right (by have := Nat.two_pow_pos f.p; omega)
      (Nat.two_pow_pos _)
  have := (Nat.log2_lt hu0).2 (Nat.lt_of_le_of_lt hmax hm)
  have := emax_pos f
  simp only [Format.t]; omega

theorem rne_rep (f : Format) (neg : Bool) (N D : Nat) :
    RepU f (roundUnits f .nearestTiesToEven neg N D) := by
  obtain ⟨hc1, -⟩ := trunc_bounds f N D
  rw [rne_unfold]
  generalize ulpExp f (N / D) = j at *
  generalize N / (D * 2 ^ j) = c at *
  split
  · by_cases h : c + 1 < 2 ^ f.p
    · exact ⟨c + 1, j, h, rfl⟩
    · refine ⟨2 ^ (f.p - 1), j + 1, ?_, ?_⟩
      · have := two_pow_pred f; have := Nat.two_pow_pos (f.p - 1); omega
      · have : c + 1 = 2 ^ f.p := by omega
        rw [this, two_pow_pred, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2]
  · exact ⟨c, j, hc1, rfl⟩

theorem zero_rep (f : Format) : RepU f 0 := ⟨0, 0, Nat.two_pow_pos _, rfl⟩

theorem maxUnits_eq (f : Format) :
    f.maxUnits = (2 ^ f.p - 1) * 2 ^ (2 * f.emax - 1) := rfl

theorem maxUnits_rep (f : Format) : RepU f f.maxUnits :=
  ⟨2 ^ f.p - 1, _, by have := Nat.two_pow_pos f.p; omega, rfl⟩

/-- The next representable magnitude above `maxUnits` (unbounded exponent) is `2^(p+J)`. -/
theorem rep_above_max (f : Format) (w : Nat) (hw : RepU f w) (h : f.maxUnits < w) :
    2 ^ (f.p + (2 * f.emax - 1)) ≤ w := by
  obtain ⟨c, i, hc, rfl⟩ := hw
  rw [maxUnits_eq] at h
  generalize 2 * f.emax - 1 = J at *
  have hp := f.hp
  by_cases hi : i ≤ J
  · exfalso
    have : c * 2 ^ i ≤ (2 ^ f.p - 1) * 2 ^ J :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) hi)
    omega
  · have e : c * 2 ^ i = c * 2 ^ (i - (J + 1)) * 2 ^ J * 2 := by
      rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_succ, ← Nat.pow_add]; congr 2; omega
    rw [e] at h ⊢
    generalize c * 2 ^ (i - (J + 1)) = m at *
    have h2 : (2 ^ f.p - 1) * 2 ^ J < m * 2 * 2 ^ J := by
      rw [Nat.mul_right_comm]; exact h
    have h3 := Nat.lt_of_mul_lt_mul_right h2
    have hp2 := two_pow_pred f
    have hm : 2 ^ (f.p - 1) ≤ m := by omega
    calc 2 ^ (f.p + J) = 2 ^ (f.p - 1) * 2 ^ J * 2 := by
          rw [Nat.mul_right_comm, ← two_pow_pred, ← Nat.pow_add]
      _ ≤ m * 2 ^ J * 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hm)

theorem not_evenSig_max (f : Format) : ¬ EvenSig f f.maxUnits := by
  have hp := f.hp
  have hp2 := two_pow_pred f
  have hpos := Nat.two_pow_pos (f.p - 1)
  have hodd : (2 ^ f.p - 1) % 2 = 1 := by omega
  have h0 : 2 ^ f.p - 1 ≠ 0 := by omega
  have hl : (2 ^ f.p - 1).log2 = f.p - 1 := by
    rw [Nat.log2_eq_iff h0, show f.p - 1 + 1 = f.p by omega]
    omega
  unfold EvenSig ulpExp
  rw [maxUnits_eq, log2_mul_two_pow _ h0, hl,
    show f.p - 1 + (2 * f.emax - 1) + 1 - f.p = 2 * f.emax - 1 by omega,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _), hodd]
  decide

/-- **Overflow threshold, in units** (§4.3.1, §7.4): the roundTiesToEven result with unbounded
exponent exceeds `maxUnits` iff `N / D ≥ maxUnits + 2^(J−1)`, where `J = 2·emax − 1` and
`2^J` is the spacing of the top binade. -/
theorem rne_overflow_iff (f : Format) (neg : Bool) (N D : Nat) (hD : 0 < D) :
    f.maxUnits < roundUnits f .nearestTiesToEven neg N D ↔
      D * (2 * f.maxUnits + 2 ^ (2 * f.emax - 1)) ≤ 2 * N := by
  have hp := f.hp
  have he := emax_pos f
  have hvrep := rne_rep f neg N D
  have hnear := rne_nearest f neg N D hD
  have htie := rne_tie_even f neg N D hD
  generalize roundUnits f .nearestTiesToEven neg N D = v at *
  have hmaxeq := maxUnits_eq f
  have habove := rep_above_max f
  have hJ1 : 1 ≤ 2 * f.emax - 1 := by omega
  generalize 2 * f.emax - 1 = J at *
  have hwrep : RepU f (2 ^ (f.p + J)) :=
    ⟨2 ^ (f.p - 1), J + 1, by have := two_pow_pred f; have := Nat.two_pow_pos (f.p - 1); omega,
      by rw [← Nat.pow_add]; congr 1; omega⟩
  -- 2^(p+J) = maxUnits + 2^J and 2^J = 2·2^(J−1)
  have hmax : f.maxUnits + 2 ^ J = 2 ^ (f.p + J) := by
    rw [hmaxeq, Nat.pow_add, Nat.sub_mul, Nat.one_mul]
    have := Nat.le_mul_of_pos_left (2 ^ J) (Nat.two_pow_pos f.p); omega
  have hJh : 2 ^ J = 2 * 2 ^ (J - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have e1 : 2 ^ (f.p + J) * D = f.maxUnits * D + 2 * (2 ^ (J - 1) * D) := by
    rw [← hmax, Nat.add_mul, hJh, Nat.mul_assoc]
  have e2 : D * (2 * f.maxUnits + 2 ^ J) = 2 * (f.maxUnits * D) + 2 * (2 ^ (J - 1) * D) := by
    rw [hJh]; simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
  rw [e2]
  have hmD := hnear _ (maxUnits_rep f)
  have hwD := hnear _ hwrep
  unfold udist at hmD hwD
  rw [e1] at hwD
  constructor
  · intro hgt
    have hvD := Nat.mul_le_mul_right D (habove v hvrep hgt)
    rw [e1] at hvD
    have hlt : f.maxUnits * D < v * D := Nat.mul_lt_mul_of_pos_right hgt hD
    generalize f.maxUnits * D = B at *
    generalize v * D = V at *
    generalize 2 ^ (J - 1) * D = A at *
    omega
  · intro hge
    apply Classical.byContradiction
    intro hle
    have hle : v ≤ f.maxUnits := by omega
    have hvD := Nat.mul_le_mul_right D hle
    by_cases hvm : v = f.maxUnits
    · -- v = maxUnits: then N/D is exactly the midpoint (else 2^(p+J) would be closer), a tie
      -- that ties-to-even must break towards the even 2^(p+J), not the odd maxUnits
      subst hvm
      apply not_evenSig_max f
      have h2J := Nat.two_pow_pos J
      apply htie (2 ^ (f.p + J)) hwrep (by rw [← hmax]; omega)
      unfold udist
      rw [e1]
      generalize f.maxUnits * D = B at *
      generalize 2 ^ (J - 1) * D = A at *
      omega
    · have hlt : v * D < f.maxUnits * D := Nat.mul_lt_mul_of_pos_right (by omega) hD
      generalize f.maxUnits * D = B at *
      generalize v * D = V at *
      generalize 2 ^ (J - 1) * D = A at *
      omega

theorem ulpExp_mul (f : Format) (c j : Nat) (h0 : 0 < c) (hc : c < 2 ^ f.p)
    (hn : 0 < j → 2 ^ (f.p - 1) ≤ c) : ulpExp f (c * 2 ^ j) = j := by
  have hp := f.hp
  unfold ulpExp
  rw [log2_mul_two_pow j (by omega)]
  have hl : c.log2 < f.p := (Nat.log2_lt (by omega)).2 hc
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · omega
  · have hl2 : f.p - 1 ≤ c.log2 := (Nat.le_log2 (by omega)).2 (hn hj)
    omega

theorem evenSig_iff (f : Format) (c j : Nat) (h0 : 0 < c) (hc : c < 2 ^ f.p)
    (hn : 0 < j → 2 ^ (f.p - 1) ≤ c) : EvenSig f (c * 2 ^ j) ↔ c % 2 = 0 := by
  unfold EvenSig
  rw [ulpExp_mul f c j h0 hc hn, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- The two neighbours `c·2^j` and `(c+1)·2^j` never both have even significands. -/
theorem not_both_even (f : Format) (c j : Nat) (hc : c < 2 ^ f.p)
    (hn : 0 < j → 2 ^ (f.p - 1) ≤ c) (h1 : EvenSig f (c * 2 ^ j))
    (h2 : EvenSig f ((c + 1) * 2 ^ j)) : False := by
  have hp := f.hp
  have hp2 := two_pow_pred f
  have hpos := Nat.two_pow_pos (f.p - 1)
  rcases Nat.eq_zero_or_pos c with rfl | h0
  · -- then j = 0, and the upper neighbour is 1 unit, whose significand 1 is odd
    have hj : j = 0 := by
      rcases Nat.eq_zero_or_pos j with h | h
      · exact h
      · have := hn h; omega
    subst hj
    rw [evenSig_iff f (0 + 1) 0 (by omega) (by omega) (by omega)] at h2
    omega
  · rw [evenSig_iff f c j h0 hc hn] at h1
    by_cases hc1 : c + 1 < 2 ^ f.p
    · rw [evenSig_iff f (c + 1) j (by omega) hc1 (fun hj => by have := hn hj; omega)] at h2
      omega
    · -- c = 2^p − 1 is odd
      omega

/-- The only representable magnitudes at most as far from `N / D` as the roundTiesToEven
result are its two neighbours `c·2^j` and `(c+1)·2^j`. -/
theorem rne_near_two (f : Format) (neg : Bool) (N D : Nat) (hD : 0 < D) (w : Nat)
    (hw : RepU f w)
    (hle : udist N D w ≤ udist N D (roundUnits f .nearestTiesToEven neg N D)) :
    w = N / (D * 2 ^ ulpExp f (N / D)) * 2 ^ ulpExp f (N / D) ∨
      w = (N / (D * 2 ^ ulpExp f (N / D)) + 1) * 2 ^ ulpExp f (N / D) := by
  obtain ⟨-, hc2⟩ := trunc_bounds f N D
  rw [rne_unfold] at hle
  generalize ulpExp f (N / D) = j at *
  have hM : 0 < D * 2 ^ j := Nat.mul_pos hD (Nat.two_pow_pos _)
  have hdm := Nat.div_add_mod N (D * 2 ^ j)
  have hr := Nat.mod_lt N hM
  generalize N / (D * 2 ^ j) = c at *
  generalize N % (D * 2 ^ j) = r at *
  have hg := gap f c j w hc2 hw
  have e1 : c * 2 ^ j * D = D * 2 ^ j * c := by ac_rfl
  have e2 : (c + 1) * 2 ^ j * D = D * 2 ^ j * c + D * 2 ^ j := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; ac_rfl
  rcases hg with h | h
  · rcases Nat.lt_or_eq_of_le h with h | h
    · exfalso
      have := e1 ▸ Nat.mul_le_mul_right D (Nat.succ_le_of_lt h)
      rw [Nat.succ_mul] at this
      unfold udist at hle
      generalize D * 2 ^ j * c = X at *
      generalize D * 2 ^ j = M at *
      split at hle <;> omega
    · exact .inl h
  · rcases Nat.lt_or_eq_of_le h with h | h
    · exfalso
      have := Nat.mul_le_mul_right D (Nat.succ_le_of_lt h)
      rw [Nat.succ_mul, e2] at this
      unfold udist at hle
      generalize D * 2 ^ j * c = X at *
      generalize D * 2 ^ j = M at *
      split at hle <;> omega
    · exact .inr h.symm

/-- No representable magnitude other than the roundTiesToEven result is as near to `N / D`
and has an even significand. -/
theorem rne_two_even (f : Format) (neg : Bool) (N D : Nat) (hD : 0 < D) (w : Nat)
    (hw : RepU f w) (hne : w ≠ roundUnits f .nearestTiesToEven neg N D)
    (hle : udist N D w ≤ udist N D (roundUnits f .nearestTiesToEven neg N D))
    (hev : EvenSig f w) : False := by
  have hstar := rne_tie_even f neg N D hD w hw hne hle
  have h2 := rne_near_two f neg N D hD w hw hle
  obtain ⟨hc1, hc2⟩ := trunc_bounds f N D
  rw [rne_unfold] at hne hstar
  generalize ulpExp f (N / D) = j at *
  generalize N / (D * 2 ^ j) = c at *
  split at hstar
  · next hup =>
    rw [if_pos hup] at hne
    rcases h2 with rfl | h
    · exact not_both_even f c j hc1 hc2 hev hstar
    · exact hne h
  · next hup =>
    rw [if_neg hup] at hne
    rcases h2 with h | rfl
    · exact hne h
    · exact not_both_even f c j hc1 hc2 hstar hev

/-- **`roundUnits` only sees the ratio**: scaling the exact quotient's numerator
and denominator by the same power of two does not change the rounded
magnitude, in every rounding mode. (It uses only `N / D`, `N / M`, `N % M`
and comparisons of `2·(N % M)` with `M`, all of which scale together.) This
removes the operands' exponents from a rounding certificate. -/
theorem roundUnits_scale (f : Format) (mode : RoundingMode) (neg : Bool) (N D k : Nat) :
    roundUnits f mode neg (N * 2 ^ k) (D * 2 ^ k) = roundUnits f mode neg N D := by
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  simp only [roundUnits, Nat.mul_div_mul_right N D hk]
  generalize ulpExp f (N / D) = j
  rw [Nat.mul_right_comm D (2 ^ k) (2 ^ j), Nat.mul_div_mul_right N _ hk,
    Nat.mul_mod_mul_right]
  generalize D * 2 ^ j = M
  generalize N / M = c
  generalize N % M = r
  have hlt : (M * 2 ^ k < 2 * (r * 2 ^ k)) = (M < 2 * r) := by
    rw [← Nat.mul_assoc]; exact propext (Nat.mul_lt_mul_right hk)
  have hle : (M * 2 ^ k ≤ 2 * (r * 2 ^ k)) = (M ≤ 2 * r) := by
    rw [← Nat.mul_assoc]; exact propext (Nat.mul_le_mul_right_iff hk)
  have heq : (2 * (r * 2 ^ k) = M * 2 ^ k) = (2 * r = M) := by
    rw [← Nat.mul_assoc]; exact propext (Nat.mul_left_inj (Nat.pos_iff_ne_zero.mp hk))
  have hz : (r * 2 ^ k = 0) = (r = 0) :=
    propext ⟨fun h => (Nat.mul_eq_zero.mp h).resolve_right (Nat.pos_iff_ne_zero.mp hk),
      fun h => by rw [h, Nat.zero_mul]⟩
  cases mode <;> simp [hlt, hle, heq, hz]

/-- **The certificate interval characterizes the roundTiesToEven result.** `u` is a
representable magnitude with an upper neighbour at distance `up` and a lower neighbour at
distance `dn` (nothing representable strictly between), and `par` says that `u`'s significand
is even. Then `u` is the roundTiesToEven magnitude of `N / D` iff `N / D` lies within half a
spacing of `u` on each side, a boundary allowed only if `par`. -/
theorem rne_eq_iff (f : Format) (s : Bool) (N D u up dn : Nat) (par : Bool) (hD : 0 < D)
    (hup0 : 0 < up) (hdn0 : 0 < dn)
    (hu : RepU f u) (hup : RepU f (u + up))
    (hdn : u ≠ 0 → dn ≤ u ∧ RepU f (u - dn))
    (nhi : ∀ w, RepU f w → w ≤ u ∨ u + up ≤ w)
    (nlo : u ≠ 0 → ∀ w, RepU f w → w ≤ u - dn ∨ u ≤ w)
    (hev : EvenSig f u ↔ par = true) :
    (u = roundUnits f .nearestTiesToEven s N D) ↔
      ((u = 0 ∨ leB par (D * (2 * u - dn)) (2 * N)) ∧ leB par (2 * N) (D * (2 * u + up))) := by
  have hnear := rne_nearest f s N D hD
  have htie := rne_tie_even f s N D hD
  have hrep := rne_rep f s N D
  have htwo := rne_two_even f s N D hD
  generalize roundUnits f .nearestTiesToEven s N D = v at *
  have hDup : 0 < up * D := Nat.mul_pos hup0 hD
  have hDdn : 0 < dn * D := Nat.mul_pos hdn0 hD
  have eU : D * (2 * u + up) = 2 * (u * D) + up * D := by
    rw [Nat.mul_add]; ac_rfl
  have eUp : (u + up) * D = u * D + up * D := Nat.add_mul _ _ _
  have eL : u ≠ 0 → D * (2 * u - dn) = (u - dn) * D + u * D ∧ (u - dn) * D + dn * D = u * D := by
    intro h0
    obtain ⟨h1, -⟩ := hdn h0
    constructor
    · rw [show 2 * u - dn = (u - dn) + u by omega, Nat.mul_add]; ac_rfl
    · rw [← Nat.add_mul, Nat.sub_add_cancel h1]
  constructor
  · intro h
    subst h
    have hhi : leB par (2 * N) (D * (2 * u + up)) := by
      have h1 := hnear (u + up) hup
      unfold udist at h1
      rw [eUp] at h1
      rw [eU]
      by_cases hp : par = true
      · rw [leB_of_eq hp]; omega
      · rw [leB_of_ne hp]
        refine Classical.byContradiction fun hge => ?_
        apply hp
        apply hev.mp
        apply htie (u + up) hup (by omega)
        unfold udist
        rw [eUp]
        omega
    refine ⟨?_, hhi⟩
    by_cases hu0 : u = 0
    · exact .inl hu0
    · right
      obtain ⟨hdle, hrepd⟩ := hdn hu0
      obtain ⟨e1, e2⟩ := eL hu0
      have h1 := hnear (u - dn) hrepd
      unfold udist at h1
      rw [e1]
      by_cases hp : par = true
      · rw [leB_of_eq hp]; omega
      · rw [leB_of_ne hp]
        refine Classical.byContradiction fun hge => ?_
        apply hp
        apply hev.mp
        apply htie (u - dn) hrepd (by omega)
        unfold udist
        omega
  · rintro ⟨hlo, hhi⟩
    refine Classical.byContradiction fun hne => ?_
    have hn1 := hnear u hu
    unfold udist at hn1
    rcases nhi v hrep with hv | hv
    · have hu0 : u ≠ 0 := by omega
      obtain ⟨hdle, hrepd⟩ := hdn hu0
      have hvlo : v ≤ u - dn := by
        rcases nlo hu0 v hrep with h | h
        · exact h
        · omega
      have hVD : v * D ≤ (u - dn) * D := Nat.mul_le_mul_right D hvlo
      obtain ⟨e1, e2⟩ := eL hu0
      have hlo' := hlo.resolve_left hu0
      rw [e1] at hlo'
      by_cases hp : par = true
      · rw [leB_of_eq hp] at hlo'
        have hle : udist N D u ≤ udist N D v := by unfold udist; omega
        exact htwo u hu hne hle (hev.mpr hp)
      · rw [leB_of_ne hp] at hlo'
        omega
    · have hVD : (u + up) * D ≤ v * D := Nat.mul_le_mul_right D hv
      rw [eUp] at hVD
      rw [eU] at hhi
      by_cases hp : par = true
      · rw [leB_of_eq hp] at hhi
        have hle : udist N D u ≤ udist N D v := by unfold udist; omega
        exact htwo u hu hne hle (hev.mpr hp)
      · rw [leB_of_ne hp] at hhi
        omega

theorem rep_succ (f : Format) (c j : Nat) (hc : c < 2 ^ f.p) :
    RepU f (c * 2 ^ j + 2 ^ j) := by
  have e : c * 2 ^ j + 2 ^ j = (c + 1) * 2 ^ j := by rw [Nat.succ_mul]
  rw [e]
  by_cases h : c + 1 < 2 ^ f.p
  · exact ⟨c + 1, j, h, rfl⟩
  · refine ⟨2 ^ (f.p - 1), j + 1, ?_, ?_⟩
    · have := two_pow_pred f; have := Nat.two_pow_pos (f.p - 1); omega
    · have : c + 1 = 2 ^ f.p := by omega
      rw [this, two_pow_pred, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2]

/-- The canonical instance of `rne_eq_iff`: `u = c·2^j` with `c` a `p`-bit significand (or
`j = 0`), upper neighbour at `2^j`, lower neighbour at `2^j`, or `2^(j-1)` at the bottom of a
binade (`c = 2^(p-1)`, `j > 0`). -/
theorem rne_eq_iff_canon (f : Format) (s : Bool) (N D c j u up dn : Nat) (par : Bool)
    (hD : 0 < D) (hc : c < 2 ^ f.p) (hc0 : 0 < c) (hj : 0 < j → 2 ^ (f.p - 1) ≤ c)
    (hu : u = c * 2 ^ j) (hup : up = 2 ^ j)
    (hdn : dn = if c = 2 ^ (f.p - 1) ∧ 0 < j then 2 ^ (j - 1) else 2 ^ j)
    (hev : c % 2 = 0 ↔ par = true) :
    (u = roundUnits f .nearestTiesToEven s N D) ↔
      ((u = 0 ∨ leB par (D * (2 * u - dn)) (2 * N)) ∧ leB par (2 * N) (D * (2 * u + up))) := by
  subst hu hup hdn
  have hp := f.hp
  have hp2 := two_pow_pred f
  have hpos := Nat.two_pow_pos (f.p - 1)
  have hj0 := Nat.two_pow_pos j
  have hdn0 : 0 < (if c = 2 ^ (f.p - 1) ∧ 0 < j then 2 ^ (j - 1) else 2 ^ j) := by
    split <;> exact Nat.two_pow_pos _
  refine rne_eq_iff f s N D _ _ _ par hD hj0 hdn0 ⟨c, j, hc, rfl⟩ (rep_succ f c j hc) ?_ ?_ ?_
    ((evenSig_iff f c j hc0 hc hj).trans hev)
  · intro _
    by_cases hb : c = 2 ^ (f.p - 1) ∧ 0 < j
    · rw [if_pos hb]
      obtain ⟨hc', hj'⟩ := hb
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hi : i + 1 - 1 = i := by omega
      have e1 : (2 ^ f.p - 1) * 2 ^ i + 2 ^ i = c * 2 ^ (i + 1) := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_two_pow), hc', hp2, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2]
      have e2 : 2 ^ i ≤ c * 2 ^ (i + 1) := by omega
      rw [hi]
      exact ⟨e2, ⟨2 ^ f.p - 1, i, by omega, by omega⟩⟩
    · rw [if_neg hb]
      have e1 : c * 2 ^ j - 2 ^ j = (c - 1) * 2 ^ j := by
        rw [Nat.sub_mul, Nat.one_mul]
      exact ⟨Nat.le_mul_of_pos_left _ hc0, ⟨c - 1, j, by omega, e1⟩⟩
  · intro w hw
    rcases gap f c j w hj hw with h | h
    · exact .inl h
    · exact .inr (by rw [Nat.succ_mul] at h; exact h)
  · intro _ w hw
    by_cases hb : c = 2 ^ (f.p - 1) ∧ 0 < j
    · rw [if_pos hb]
      obtain ⟨hc', hj'⟩ := hb
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hi : i + 1 - 1 = i := by omega
      have e1 : (2 ^ f.p - 1) * 2 ^ i + 2 ^ i = c * 2 ^ (i + 1) := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_two_pow), hc', hp2, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2]
      rw [hi]
      rcases gap f (2 ^ f.p - 1) i w (fun _ => by omega) hw with h | h
      · exact .inl (by omega)
      · have e3 : 2 ^ f.p * 2 ^ i = c * 2 ^ (i + 1) := by
          rw [hc', hp2, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2]
        exact .inr (by rw [Nat.sub_add_cancel Nat.one_le_two_pow] at h; omega)
    · rw [if_neg hb]
      rcases gap f (c - 1) j w (fun hj' => by omega) hw with h | h
      · exact .inl (by rw [Nat.sub_mul, Nat.one_mul] at h; exact h)
      · exact .inr (by rw [Nat.sub_add_cancel hc0] at h; exact h)

/-! ## The five rounding-direction attributes, declaratively (§4.3.1, §4.3.2)

`IsRoundedTo f mode neg N D u`: `u` units is a correctly rounded magnitude of the exact magnitude `N / D` units under
`mode`, for a result of sign `neg`, with unbounded exponent range (the overflow results of §7.4 are `round`'s, and
`rne_overflow_iff` gives roundTiesToEven's threshold). It names no algorithm: `u` is representable (`RepU`) and

* roundTiesToEven: no representable magnitude is nearer, and if another one is as near, `u`'s significand is even;
* roundTiesToAway: no representable magnitude is nearer, and if another one is as near, it is smaller than `u`;
* roundTowardZero: the largest representable magnitude not above `N / D` (`RoundsDown`);
* roundTowardPositive / roundTowardNegative: the magnitude rounded up (`RoundsUp`) when the direction points away from
  zero for this sign, down otherwise.

`roundUnits_isRoundedTo`: `roundUnits` meets it, for every format, attribute and sign. -/

/-- `u` is at most `N / D` and nothing representable lies strictly between `u` and `N / D` or at `N / D` above `u`:
the magnitude rounded down. -/
def RoundsDown (f : Format) (N D u : Nat) : Prop := u * D ≤ N ∧ ∀ w, RepU f w → w * D ≤ N → w ≤ u

/-- `u` is at least `N / D` and nothing representable lies at or above `N / D` below `u`: the magnitude rounded up. -/
def RoundsUp (f : Format) (N D u : Nat) : Prop := N ≤ u * D ∧ ∀ w, RepU f w → N ≤ w * D → u ≤ w

/-- No representable magnitude is nearer to `N / D` than `u` (distances times `D`, `udist`). -/
def IsNearestU (f : Format) (N D u : Nat) : Prop := ∀ w, RepU f w → udist N D u ≤ udist N D w

/-- `u` is a correctly rounded magnitude of `N / D` under `mode` for a result of sign `neg` (§4.3.1, §4.3.2). -/
def IsRoundedTo (f : Format) (mode : RoundingMode) (neg : Bool) (N D u : Nat) : Prop :=
  RepU f u ∧
  match mode, neg with
  | .nearestTiesToEven, _ =>
    IsNearestU f N D u ∧ ∀ w, RepU f w → w ≠ u → udist N D w ≤ udist N D u → EvenSig f u
  | .nearestTiesToAway, _ =>
    IsNearestU f N D u ∧ ∀ w, RepU f w → w ≠ u → udist N D w ≤ udist N D u → w < u
  | .towardZero, _ => RoundsDown f N D u
  | .towardPositive, false => RoundsUp f N D u
  | .towardPositive, true => RoundsDown f N D u
  | .towardNegative, false => RoundsDown f N D u
  | .towardNegative, true => RoundsUp f N D u

/-- The bracket of `N / D` that `roundUnits` reads: `j = ulpExp ⌊N/D⌋`, `N = (D·2^j)·c + r`, `r < D·2^j`, with `c`
a significand of at most `p` bits (exactly `p` when `j > 0`). -/
theorem bracket (f : Format) (N D : Nat) (hD : 0 < D) :
    ∃ j c r, ulpExp f (N / D) = j ∧ N / (D * 2 ^ j) = c ∧ N % (D * 2 ^ j) = r ∧
      D * 2 ^ j * c + r = N ∧ r < D * 2 ^ j ∧ c < 2 ^ f.p ∧ (0 < j → 2 ^ (f.p - 1) ≤ c) := by
  obtain ⟨hc1, hc2⟩ := trunc_bounds f N D
  exact ⟨_, _, _, rfl, rfl, rfl, Nat.div_add_mod _ _, Nat.mod_lt _ (Nat.mul_pos hD (Nat.two_pow_pos _)), hc1, hc2⟩

theorem roundsDown_lo (f : Format) (N D j c r : Nat) (hdm : D * 2 ^ j * c + r = N) (hr : r < D * 2 ^ j)
    (hc2 : 0 < j → 2 ^ (f.p - 1) ≤ c) : RoundsDown f N D (c * 2 ^ j) := by
  unfold RoundsDown
  have e1 : c * 2 ^ j * D = D * 2 ^ j * c := by ac_rfl
  refine ⟨by rw [e1]; omega, fun w hw hwN => ?_⟩
  rcases gap f c j w hc2 hw with h | h
  · exact h
  · exfalso
    have h' := Nat.mul_le_mul_right D h
    have e2 : (c + 1) * 2 ^ j * D = D * 2 ^ j * c + D * 2 ^ j := by
      rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; ac_rfl
    rw [e2] at h'
    generalize D * 2 ^ j * c = X at *
    generalize D * 2 ^ j = M at *
    omega

theorem roundsUp_exact (f : Format) (N D j c : Nat) (hD : 0 < D) (hdm : D * 2 ^ j * c = N)
    (hc2 : 0 < j → 2 ^ (f.p - 1) ≤ c) : RoundsUp f N D (c * 2 ^ j) := by
  unfold RoundsUp
  have e1 : c * 2 ^ j * D = D * 2 ^ j * c := by ac_rfl
  refine ⟨by rw [e1]; omega, fun w hw hwN => ?_⟩
  rcases gap f c j w hc2 hw with h | h
  · exact Nat.le_of_mul_le_mul_right (by rw [e1]; omega) hD
  · exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_succ c)) h

theorem roundsUp_inexact (f : Format) (N D j c r : Nat) (hdm : D * 2 ^ j * c + r = N)
    (hr : r < D * 2 ^ j) (hr0 : r ≠ 0) (hc2 : 0 < j → 2 ^ (f.p - 1) ≤ c) :
    RoundsUp f N D ((c + 1) * 2 ^ j) := by
  unfold RoundsUp
  have e1 : c * 2 ^ j * D = D * 2 ^ j * c := by ac_rfl
  have e2 : (c + 1) * 2 ^ j * D = D * 2 ^ j * c + D * 2 ^ j := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; ac_rfl
  refine ⟨by rw [e2]; omega, fun w hw hwN => ?_⟩
  rcases gap f c j w hc2 hw with h | h
  · exfalso
    have h' := Nat.mul_le_mul_right D h
    rw [e1] at h'
    generalize D * 2 ^ j * c = X at *
    omega
  · exact h

theorem nearest_lo (f : Format) (N D j c r : Nat) (hdm : D * 2 ^ j * c + r = N) (hr : r < D * 2 ^ j)
    (hc2 : 0 < j → 2 ^ (f.p - 1) ≤ c) (h2 : 2 * r ≤ D * 2 ^ j) : IsNearestU f N D (c * 2 ^ j) := by
  intro w hw
  have e1 : c * 2 ^ j * D = D * 2 ^ j * c := by ac_rfl
  have e2 : (c + 1) * 2 ^ j * D = D * 2 ^ j * c + D * 2 ^ j := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; ac_rfl
  have hg : w * D ≤ D * 2 ^ j * c ∨ D * 2 ^ j * c + D * 2 ^ j ≤ w * D := by
    rcases gap f c j w hc2 hw with h | h
    · exact .inl (e1 ▸ Nat.mul_le_mul_right D h)
    · exact .inr (e2 ▸ Nat.mul_le_mul_right D h)
  unfold udist
  rw [e1]
  generalize D * 2 ^ j * c = X at *
  generalize D * 2 ^ j = M at *
  omega

theorem nearest_hi (f : Format) (N D j c r : Nat) (hdm : D * 2 ^ j * c + r = N) (hr : r < D * 2 ^ j)
    (hc2 : 0 < j → 2 ^ (f.p - 1) ≤ c) (h2 : D * 2 ^ j ≤ 2 * r) :
    IsNearestU f N D ((c + 1) * 2 ^ j) := by
  intro w hw
  have e1 : c * 2 ^ j * D = D * 2 ^ j * c := by ac_rfl
  have e2 : (c + 1) * 2 ^ j * D = D * 2 ^ j * c + D * 2 ^ j := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; ac_rfl
  have hg : w * D ≤ D * 2 ^ j * c ∨ D * 2 ^ j * c + D * 2 ^ j ≤ w * D := by
    rcases gap f c j w hc2 hw with h | h
    · exact .inl (e1 ▸ Nat.mul_le_mul_right D h)
    · exact .inr (e2 ▸ Nat.mul_le_mul_right D h)
  unfold udist
  rw [e2]
  generalize D * 2 ^ j * c = X at *
  generalize D * 2 ^ j = M at *
  omega

theorem tiesAway_lo (f : Format) (N D j c r : Nat) (hdm : D * 2 ^ j * c + r = N)
    (hr : r < D * 2 ^ j) (hc2 : 0 < j → 2 ^ (f.p - 1) ≤ c) (h2 : 2 * r < D * 2 ^ j) (w : Nat)
    (hw : RepU f w) (hne : w ≠ c * 2 ^ j) (hle : udist N D w ≤ udist N D (c * 2 ^ j)) : w < c * 2 ^ j := by
  have e1 : c * 2 ^ j * D = D * 2 ^ j * c := by ac_rfl
  have e2 : (c + 1) * 2 ^ j * D = D * 2 ^ j * c + D * 2 ^ j := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; ac_rfl
  rcases gap f c j w hc2 hw with h | h
  · omega
  · exfalso
    have h' := Nat.mul_le_mul_right D h
    rw [e2] at h'
    unfold udist at hle
    rw [e1] at hle
    generalize D * 2 ^ j * c = X at *
    generalize D * 2 ^ j = M at *
    omega

theorem tiesAway_hi (f : Format) (N D j c r : Nat) (hD : 0 < D) (hdm : D * 2 ^ j * c + r = N)
    (hr : r < D * 2 ^ j) (hc2 : 0 < j → 2 ^ (f.p - 1) ≤ c) (w : Nat)
    (hw : RepU f w) (hne : w ≠ (c + 1) * 2 ^ j) (hle : udist N D w ≤ udist N D ((c + 1) * 2 ^ j)) :
    w < (c + 1) * 2 ^ j := by
  have e2 : (c + 1) * 2 ^ j * D = D * 2 ^ j * c + D * 2 ^ j := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; ac_rfl
  rcases gap f c j w hc2 hw with h | h
  · exact Nat.lt_of_le_of_lt h (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self c) (Nat.two_pow_pos j))
  · exfalso
    have hlt : (c + 1) * 2 ^ j < w := Nat.lt_of_le_of_ne h (Ne.symm hne)
    have h' := Nat.mul_lt_mul_of_pos_right hlt hD
    rw [e2] at h'
    unfold udist at hle
    rw [e2] at hle
    generalize D * 2 ^ j * c = X at *
    generalize D * 2 ^ j = M at *
    omega

/-- **`roundUnits` rounds correctly under every rounding-direction attribute** (§4.3.1, §4.3.2), for every format,
sign and exact magnitude `N / D` (`D > 0`), with unbounded exponent range. -/
theorem roundUnits_isRoundedTo (f : Format) (mode : RoundingMode) (neg : Bool) (N D : Nat) (hD : 0 < D) :
    IsRoundedTo f mode neg N D (roundUnits f mode neg N D) := by
  obtain ⟨j, c, r, hj, hc, hr, hdm, hrM, hc1, hc2⟩ := bracket f N D hD
  have hlo : RepU f (c * 2 ^ j) := ⟨c, j, hc1, rfl⟩
  have hhi : RepU f ((c + 1) * 2 ^ j) := by rw [Nat.succ_mul]; exact rep_succ f c j hc1
  cases mode with
  | nearestTiesToEven =>
    simp only [IsRoundedTo]
    exact ⟨rne_rep f neg N D, fun w hw => rne_nearest f neg N D hD w hw,
      fun w hw hne hle => rne_tie_even f neg N D hD w hw hne hle⟩
  | nearestTiesToAway =>
    by_cases h2 : D * 2 ^ j ≤ 2 * r
    · have hu : roundUnits f .nearestTiesToAway neg N D = (c + 1) * 2 ^ j := by
        simp [roundUnits, hj, hc, hr, h2]
      rw [hu]; simp only [IsRoundedTo]
      exact ⟨hhi, nearest_hi f N D j c r hdm hrM hc2 h2,
        fun w hw hne hle => tiesAway_hi f N D j c r hD hdm hrM hc2 w hw hne hle⟩
    · have hu : roundUnits f .nearestTiesToAway neg N D = c * 2 ^ j := by
        simp [roundUnits, hj, hc, hr, h2]
      rw [hu]; simp only [IsRoundedTo]
      exact ⟨hlo, nearest_lo f N D j c r hdm hrM hc2 (by omega),
        fun w hw hne hle => tiesAway_lo f N D j c r hdm hrM hc2 (by omega) w hw hne hle⟩
  | towardZero =>
    have hu : roundUnits f .towardZero neg N D = c * 2 ^ j := by simp [roundUnits, hj, hc]
    rw [hu]; simp only [IsRoundedTo]
    exact ⟨hlo, roundsDown_lo f N D j c r hdm hrM hc2⟩
  | towardPositive =>
    cases neg with
    | true =>
      have hu : roundUnits f .towardPositive true N D = c * 2 ^ j := by simp [roundUnits, hj, hc]
      rw [hu]; simp only [IsRoundedTo]
      exact ⟨hlo, roundsDown_lo f N D j c r hdm hrM hc2⟩
    | false =>
      by_cases hr0 : r = 0
      · have hu : roundUnits f .towardPositive false N D = c * 2 ^ j := by
          simp [roundUnits, hj, hc, hr, hr0]
        rw [hu]; simp only [IsRoundedTo]
        exact ⟨hlo, roundsUp_exact f N D j c hD (by omega) hc2⟩
      · have hu : roundUnits f .towardPositive false N D = (c + 1) * 2 ^ j := by
          simp [roundUnits, hj, hc, hr, hr0]
        rw [hu]; simp only [IsRoundedTo]
        exact ⟨hhi, roundsUp_inexact f N D j c r hdm hrM hr0 hc2⟩
  | towardNegative =>
    cases neg with
    | false =>
      have hu : roundUnits f .towardNegative false N D = c * 2 ^ j := by simp [roundUnits, hj, hc]
      rw [hu]; simp only [IsRoundedTo]
      exact ⟨hlo, roundsDown_lo f N D j c r hdm hrM hc2⟩
    | true =>
      by_cases hr0 : r = 0
      · have hu : roundUnits f .towardNegative true N D = c * 2 ^ j := by
          simp [roundUnits, hj, hc, hr, hr0]
        rw [hu]; simp only [IsRoundedTo]
        exact ⟨hlo, roundsUp_exact f N D j c hD (by omega) hc2⟩
      · have hu : roundUnits f .towardNegative true N D = (c + 1) * 2 ^ j := by
          simp [roundUnits, hj, hc, hr, hr0]
        rw [hu]; simp only [IsRoundedTo]
        exact ⟨hhi, roundsUp_inexact f N D j c r hdm hrM hr0 hc2⟩

end LeanModels.SoftFloat.Binary
