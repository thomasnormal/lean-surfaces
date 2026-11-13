import LeanModels.SoftFloat.Binary.Round

/-!
# The fields of a bit pattern (§3.4)

A `k`-bit pattern is `S ‖ E ‖ T`. This file reads the fields (`signF`, `expF`, `fracF`, the significand `sigF` and the
quantum exponent `qexpF` of a finite pattern, the classification `isNaNF`/`isInfF`/`isZeroF`), shows that
`fields` packs them injectively (`fields_toNat`, `fields_injF`, `eq_fields`, `msb_eq_S`), that `decode` IS the
reading by fields (`decodeF_eq`, `rfl`), and that the encoder `finite` of a magnitude `uF E T` in units gives back the
fields (`finite_uF`, `uF_of_rep`). The §5.7.2 predicates of `Defs.lean` are related to the fields here too.

Ported from svGolf's fdivp reference proof (sections `IEEE754Proofs`, `CertF`, `DpM`), the maintainers' text.
-/

namespace LeanModels.SoftFloat.Binary

open NatFacts

theorem fields_toNat (f : Format) (neg : Bool) (E T : Nat) (hE : E < 2 ^ f.w)
    (hT : T < 2 ^ f.t) :
    (fields f neg E T).toNat = (if neg then 1 else 0) * 2 ^ (f.w + f.t) + (E * 2 ^ f.t + T) := by
  have hlow : E * 2 ^ f.t + T < 2 ^ (f.w + f.t) := by
    rw [Nat.pow_add]
    have : (E + 1) * 2 ^ f.t ≤ 2 ^ f.w * 2 ^ f.t := Nat.mul_le_mul_right _ hE
    rw [Nat.succ_mul] at this; omega
  unfold fields
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Nat.add_assoc]
  have : 2 ^ f.k = 2 * 2 ^ (f.w + f.t) := by
    rw [← Nat.pow_succ']; congr 1; simp only [Format.k]; omega
  rw [this]; cases neg <;> simp <;> omega

theorem two_pow_k (f : Format) : 2 ^ f.k = 2 * 2 ^ (f.w + f.t) := by
  rw [← Nat.pow_succ']; congr 1; simp only [Format.k]; omega

/-- `BitVec.msb` is `decode`'s sign `S = 1` (`S` is the top bit of the `k = 1 + w + t` bits). -/
theorem msb_eq_S (f : Format) (a : BitVec f.k) :
    a.msb = (a.toNat / 2 ^ (f.w + f.t) == 1) := by
  have hlt : a.toNat < 2 * 2 ^ (f.w + f.t) := two_pow_k f ▸ a.isLt
  have hk : f.k - 1 = f.w + f.t := by simp only [Format.k]; omega
  have hP := Nat.two_pow_pos (f.w + f.t)
  rw [BitVec.msb_eq_decide, hk]
  by_cases h : 2 ^ (f.w + f.t) ≤ a.toNat
  · have : a.toNat / 2 ^ (f.w + f.t) = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [h, this]
  · have : a.toNat / 2 ^ (f.w + f.t) = 0 := Nat.div_eq_of_lt (by omega)
    simp [h, this]

/-- Every pattern is its fields `S ‖ E ‖ T`, with `S = msb`. -/
theorem eq_fields (f : Format) (R : BitVec f.k) :
    R = fields f R.msb (R.toNat / 2 ^ f.t % 2 ^ f.w) (R.toNat % 2 ^ f.t) := by
  have hE := Nat.mod_lt (R.toNat / 2 ^ f.t) (Nat.two_pow_pos f.w)
  have hT := Nat.mod_lt R.toNat (Nat.two_pow_pos f.t)
  apply BitVec.eq_of_toNat_eq
  rw [fields_toNat f _ _ _ hE hT, msb_eq_S]
  have hlt : R.toNat < 2 * 2 ^ (f.w + f.t) := two_pow_k f ▸ R.isLt
  have h1 := Nat.div_add_mod R.toNat (2 ^ (f.w + f.t))
  have e : 2 ^ (f.w + f.t) = 2 ^ f.t * 2 ^ f.w := by rw [Nat.pow_add, Nat.mul_comm]
  have h2 : R.toNat % 2 ^ (f.w + f.t) =
      R.toNat / 2 ^ f.t % 2 ^ f.w * 2 ^ f.t + R.toNat % 2 ^ f.t := by
    rw [e, Nat.mod_mul, Nat.add_comm, Nat.mul_comm]
  have hS : R.toNat / 2 ^ (f.w + f.t) < 2 :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by omega)
  rw [h2] at h1
  generalize R.toNat / 2 ^ (f.w + f.t) = S at *
  have : S = 0 ∨ S = 1 := by omega
  rcases this with rfl | rfl <;> simp <;> omega

theorem two_pow_t (f : Format) : 2 ^ f.p = 2 * 2 ^ f.t := by
  have := two_pow_pred f
  simp only [Format.t]; omega

theorem four_le_two_pow_w (f : Format) : 4 ≤ 2 ^ f.w := by
  have := f.hw
  calc 4 = 2 ^ 2 := rfl
    _ ≤ 2 ^ f.w := Nat.pow_le_pow_right (by omega) this

theorem two_pow_t_even (f : Format) : 2 ^ f.t % 2 = 0 := by
  have h1 : f.t = (f.t - 1) + 1 := by have := f.hp; simp only [Format.t]; omega
  rw [h1, Nat.pow_succ]; omega

/-- The biased exponent field `E` (§3.4): the `w` bits above the trailing field. -/
def expF (f : Format) (x : BitVec f.k) : Nat := x.toNat / 2 ^ f.t % 2 ^ f.w

/-- The trailing significand field `T`: the low `t = p - 1` bits. -/
def fracF (f : Format) (x : BitVec f.k) : Nat := x.toNat % 2 ^ f.t

/-- The sign bit `S`: the bit above `E ‖ T`. -/
def signF (f : Format) (x : BitVec f.k) : Bool := x.toNat / 2 ^ (f.w + f.t) == 1

/-- `x` is a NaN: `E = 2^w - 1`, `T ≠ 0`. -/
def isNaNF (f : Format) (x : BitVec f.k) : Prop := expF f x = 2 ^ f.w - 1 ∧ fracF f x ≠ 0

/-- `x` is an infinity: `E = 2^w - 1`, `T = 0`. -/
def isInfF (f : Format) (x : BitVec f.k) : Prop := expF f x = 2 ^ f.w - 1 ∧ fracF f x = 0

/-- `x` is a zero: `E = 0`, `T = 0`. -/
def isZeroF (f : Format) (x : BitVec f.k) : Prop := expF f x = 0 ∧ fracF f x = 0

instance (f : Format) (x : BitVec f.k) : Decidable (isNaNF f x) := inferInstanceAs (Decidable (_ ∧ _))

instance (f : Format) (x : BitVec f.k) : Decidable (isInfF f x) := inferInstanceAs (Decidable (_ ∧ _))

instance (f : Format) (x : BitVec f.k) : Decidable (isZeroF f x) := inferInstanceAs (Decidable (_ ∧ _))

/-- The integral significand `c` of a finite pattern (§3.3, §3.4 (c), (d)): hidden bit `E ≠ 0`
above `T`. -/
def sigF (f : Format) (x : BitVec f.k) : Nat :=
  if expF f x = 0 then fracF f x else 2 ^ f.t + fracF f x

/-- The quantum exponent `q` of a finite pattern (§3.3): `E - emax - t` for a normal number,
`emin - t = 1 - emax - t` for a subnormal, i.e. `max(E, 1) - emax - t`. -/
def qexpF (f : Format) (x : BitVec f.k) : Int :=
  (if expF f x = 0 then (1 : Int) else (expF f x : Int)) - f.emax - f.t

/-- `decode` in terms of the fields (it is literally this; `rfl`). -/
theorem decodeF_eq (f : Format) (x : BitVec f.k) :
    decode f x =
      if expF f x = 2 ^ f.w - 1 then
        (if fracF f x = 0 then .inf (signF f x) else .nan (fracF f x < 2 ^ (f.t - 1)))
      else if expF f x = 0 then
        (if fracF f x = 0 then .zero (signF f x)
         else .finite (signF f x) (f.emin - f.t) (fracF f x))
      else .finite (signF f x) ((expF f x : Int) - f.emax - f.t) (2 ^ f.t + fracF f x) := rfl

theorem signF_eq (f : Format) (x : BitVec f.k) : signF f x = x.msb := (msb_eq_S f x).symm

theorem eq_fieldsF (f : Format) (c : BitVec f.k) :
    c = fields f (signF f c) (expF f c) (fracF f c) := by
  have h := eq_fields f c
  rw [signF_eq]
  exact h

theorem expF_lt (f : Format) (x : BitVec f.k) : expF f x < 2 ^ f.w :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem fracF_lt (f : Format) (x : BitVec f.k) : fracF f x < 2 ^ f.t :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem fields_injF (f : Format) (s s' : Bool) (E E' T T' : Nat) (hE : E < 2 ^ f.w)
    (hE' : E' < 2 ^ f.w) (hT : T < 2 ^ f.t) (hT' : T' < 2 ^ f.t)
    (h : fields f s E T = fields f s' E' T') : s = s' ∧ E = E' ∧ T = T' := by
  have h1 := congrArg BitVec.toNat h
  rw [fields_toNat f s E T hE hT, fields_toNat f s' E' T' hE' hT'] at h1
  have hB := Nat.two_pow_pos f.t
  have hlow : ∀ E T : Nat, E < 2 ^ f.w → T < 2 ^ f.t → E * 2 ^ f.t + T < 2 ^ (f.w + f.t) := by
    intro E T hE hT
    rw [Nat.pow_add]
    have : (E + 1) * 2 ^ f.t ≤ 2 ^ f.w * 2 ^ f.t := Nat.mul_le_mul_right _ hE
    rw [Nat.succ_mul] at this; omega
  have hX := hlow E T hE hT
  have hX' := hlow E' T' hE' hT'
  have key : E * 2 ^ f.t + T = E' * 2 ^ f.t + T' → E = E' ∧ T = T' := by
    intro hh
    have a1 : (T + E * 2 ^ f.t) % 2 ^ f.t = T := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hT]
    have a2 : (T' + E' * 2 ^ f.t) % 2 ^ f.t = T' := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hT']
    have b1 : (T + E * 2 ^ f.t) / 2 ^ f.t = E := by
      rw [Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hT, Nat.zero_add]
    have b2 : (T' + E' * 2 ^ f.t) / 2 ^ f.t = E' := by
      rw [Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hT', Nat.zero_add]
    have hh' : T + E * 2 ^ f.t = T' + E' * 2 ^ f.t := by omega
    refine ⟨?_, ?_⟩
    · rw [← b1, ← b2, hh']
    · rw [← a1, ← a2, hh']
  generalize 2 ^ (f.w + f.t) = C at *
  cases s <;> cases s' <;> simp only [Bool.false_eq_true, ↓reduceIte] at h1 ⊢
  · have := key (by omega); exact ⟨trivial, this⟩
  · omega
  · omega
  · have := key (by omega); exact ⟨trivial, this⟩

/-- The magnitude, in units of `2^-scale`, of a pattern with fields `E < 2^w - 1`, `T`:
`T` (subnormal) or `(2^t + T)·2^(E-1)`. -/
def uF (f : Format) (E T : Nat) : Nat := if E = 0 then T else (2 ^ f.t + T) * 2 ^ (E - 1)

theorem finite_uF (f : Format) (s : Bool) (E T : Nat) (hE : E < 2 ^ f.w - 1) (hT : T < 2 ^ f.t) :
    finite f s (uF f E T) = fields f s E T := by
  have ht : f.t = f.p - 1 := rfl
  have hB := Nat.two_pow_pos f.t
  unfold finite
  by_cases hE0 : E = 0
  · subst hE0
    have : uF f 0 T = T := by simp [uF]
    rw [this, if_pos hT]
  · have hu : uF f E T = (2 ^ f.t + T) * 2 ^ (E - 1) := by simp [uF, hE0]
    rw [hu]
    have hc0 : 2 ^ f.t + T ≠ 0 := by omega
    have hlog : (2 ^ f.t + T).log2 = f.t := by
      rw [Nat.log2_eq_iff hc0, Nat.pow_succ]; omega
    have hge : ¬ (2 ^ f.t + T) * 2 ^ (E - 1) < 2 ^ f.t := by
      have := Nat.le_mul_of_pos_right (2 ^ f.t + T) (Nat.two_pow_pos (E - 1)); omega
    rw [if_neg hge]
    simp only []
    rw [log2_mul_two_pow _ hc0, hlog, show f.t + (E - 1) - f.t = E - 1 by omega,
      Nat.mul_div_cancel _ (Nat.two_pow_pos _), show E - 1 + 1 = E by omega,
      show 2 ^ f.t + T - 2 ^ f.t = T by omega]

/-- Every representable magnitude in the finite range is `uF E T` for a finite pattern. -/
theorem uF_of_rep (f : Format) (u : Nat) (hmax : u ≤ f.maxUnits) (hu : RepU f u) :
    ∃ E T, E < 2 ^ f.w - 1 ∧ T < 2 ^ f.t ∧ u = uF f E T := by
  have hw4 := four_le_two_pow_w f
  by_cases hlt : u < 2 ^ f.t
  · exact ⟨0, u, by omega, hlt, by simp [uF]⟩
  · have hu0 : u ≠ 0 := by have := Nat.two_pow_pos f.t; omega
    obtain ⟨hlo, hT, hj2⟩ := normal_bounds f u hmax (by omega)
    have hdvd := rep_dvd f u hu hu0
    generalize hj : Nat.log2 u - f.t = j at hlo hT hj2 hdvd
    refine ⟨j + 1, u / 2 ^ j - 2 ^ f.t, by omega, by omega, ?_⟩
    simp only [uF, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [show 2 ^ f.t + (u / 2 ^ j - 2 ^ f.t) = u / 2 ^ j by omega, Nat.div_mul_cancel hdvd]

theorem fields_fields (f : Format) (s : Bool) (E T : Nat) (hE : E < 2 ^ f.w) (hT : T < 2 ^ f.t) :
    signF f (fields f s E T) = s ∧ expF f (fields f s E T) = E ∧ fracF f (fields f s E T) = T := by
  have h := fields_injF f s (signF f (fields f s E T)) E (expF f (fields f s E T)) T
    (fracF f (fields f s E T)) hE (expF_lt f _) hT (fracF_lt f _)
    (eq_fieldsF f (fields f s E T))
  exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem two_pow_w_emax (f : Format) : 2 ^ f.w = 2 * f.emax + 2 := by
  have hw := f.hw
  obtain ⟨k, hk⟩ : ∃ k, f.w = k + 1 := ⟨f.w - 1, by omega⟩
  have e1 : f.w - 1 = k := by omega
  have h2 : 2 ^ (f.w - 1) = 2 ^ k := by rw [e1]
  have hpos := Nat.two_pow_pos k
  have : f.emax = 2 ^ k - 1 := by simp only [Format.emax, e1]
  rw [hk, Nat.pow_succ, this]
  omega

theorem two_pow_p1 (f : Format) : 2 ^ (f.p + 1) = 4 * 2 ^ f.t := by
  have hp := f.hp
  have e : f.p + 1 = f.t + 2 := by simp only [Format.t]; omega
  rw [e, Nat.pow_add]
  omega

/-! ## Classification (§5.7.2) by fields -/

/-- `class(x)` read from the fields: `E = 2^w − 1` a NaN (signaling iff `d₁ = 0`, §6.2.1) or an infinity, `E = 0` a
zero or a subnormal, otherwise a normal number; the sign bit gives the sign of every non-NaN class. -/
theorem classify_eq (f : Format) (x : BitVec f.k) :
    classify f x =
      if expF f x = 2 ^ f.w - 1 then
        (if fracF f x = 0 then (if signF f x then .negativeInfinity else .positiveInfinity)
         else if fracF f x < 2 ^ (f.t - 1) then .signalingNaN else .quietNaN)
      else if expF f x = 0 then
        (if fracF f x = 0 then (if signF f x then .negativeZero else .positiveZero)
         else if signF f x then .negativeSubnormal else .positiveSubnormal)
      else if signF f x then .negativeNormal else .positiveNormal := by
  have he : x.toNat / 2 ^ f.t % 2 ^ f.w = expF f x := rfl
  have hw0 : 2 ^ f.w - 1 ≠ 0 := by have := four_le_two_pow_w f; omega
  unfold classify
  rw [decodeF_eq, he]
  by_cases h1 : expF f x = 2 ^ f.w - 1
  · simp only [if_pos h1]
    by_cases h3 : fracF f x = 0
    · simp only [if_pos h3] <;> cases signF f x <;> rfl
    · simp only [if_neg h3]
      all_goals (by_cases h4 : fracF f x < 2 ^ (f.t - 1) <;> simp [h4])
  · simp only [if_neg h1]
    by_cases h2 : expF f x = 0
    · simp only [if_pos h2]
      by_cases h3 : fracF f x = 0
      · simp only [if_pos h3] <;> cases signF f x <;> rfl
      · simp only [if_neg h3] <;> cases signF f x <;> rfl
    · simp only [if_neg h2] <;> cases signF f x <;> rfl

/-- §5.7.2 `isNaN` is the field test `isNaNF`. -/
theorem isNaN_iff (f : Format) (x : BitVec f.k) : isNaN f x = true ↔ isNaNF f x := by
  have hw0 : 2 ^ f.w - 1 ≠ 0 := by have := four_le_two_pow_w f; omega
  unfold isNaN isNaNF
  rw [classify_eq]
  by_cases h1 : expF f x = 2 ^ f.w - 1
  · rw [if_pos h1]
    by_cases h3 : fracF f x = 0
    · rw [if_pos h3]; cases signF f x <;> simp [h1, h3, hw0, Ne.symm hw0] <;> omega
    · rw [if_neg h3]
      by_cases h4 : fracF f x < 2 ^ (f.t - 1)
      · rw [if_pos h4]; simp [h1, h3, hw0, Ne.symm hw0] <;> omega
      · rw [if_neg h4]; simp [h1, h3, hw0, Ne.symm hw0] <;> omega
  · rw [if_neg h1]
    by_cases h2 : expF f x = 0
    · rw [if_pos h2]
      by_cases h3 : fracF f x = 0
      · rw [if_pos h3]; cases signF f x <;> simp [h1, h2, h3, hw0, Ne.symm hw0] <;> omega
      · rw [if_neg h3]; cases signF f x <;> simp [h1, h2, h3, hw0, Ne.symm hw0] <;> omega
    · rw [if_neg h2]; cases signF f x <;> simp [h1, h2, hw0, Ne.symm hw0] <;> omega

/-- §5.7.2 `isInfinite` is the field test `isInfF`. -/
theorem isInfinite_iff (f : Format) (x : BitVec f.k) : isInfinite f x = true ↔ isInfF f x := by
  have hw0 : 2 ^ f.w - 1 ≠ 0 := by have := four_le_two_pow_w f; omega
  unfold isInfinite isInfF
  rw [classify_eq]
  by_cases h1 : expF f x = 2 ^ f.w - 1
  · rw [if_pos h1]
    by_cases h3 : fracF f x = 0
    · rw [if_pos h3]; cases signF f x <;> simp [h1, h3, hw0, Ne.symm hw0] <;> omega
    · rw [if_neg h3]
      by_cases h4 : fracF f x < 2 ^ (f.t - 1)
      · rw [if_pos h4]; simp [h1, h3, hw0, Ne.symm hw0] <;> omega
      · rw [if_neg h4]; simp [h1, h3, hw0, Ne.symm hw0] <;> omega
  · rw [if_neg h1]
    by_cases h2 : expF f x = 0
    · rw [if_pos h2]
      by_cases h3 : fracF f x = 0
      · rw [if_pos h3]; cases signF f x <;> simp [h1, h2, h3, hw0, Ne.symm hw0] <;> omega
      · rw [if_neg h3]; cases signF f x <;> simp [h1, h2, h3, hw0, Ne.symm hw0] <;> omega
    · rw [if_neg h2]; cases signF f x <;> simp [h1, h2, hw0, Ne.symm hw0] <;> omega

/-- §5.7.2 `isZero` is the field test `isZeroF`. -/
theorem isZero_iff (f : Format) (x : BitVec f.k) : isZero f x = true ↔ isZeroF f x := by
  have hw0 : 2 ^ f.w - 1 ≠ 0 := by have := four_le_two_pow_w f; omega
  unfold isZero isZeroF
  rw [classify_eq]
  by_cases h1 : expF f x = 2 ^ f.w - 1
  · rw [if_pos h1]
    by_cases h3 : fracF f x = 0
    · rw [if_pos h3]; cases signF f x <;> simp [h1, h3, hw0, Ne.symm hw0] <;> omega
    · rw [if_neg h3]
      by_cases h4 : fracF f x < 2 ^ (f.t - 1)
      · rw [if_pos h4]; simp [h1, h3, hw0, Ne.symm hw0] <;> omega
      · rw [if_neg h4]; simp [h1, h3, hw0, Ne.symm hw0] <;> omega
  · rw [if_neg h1]
    by_cases h2 : expF f x = 0
    · rw [if_pos h2]
      by_cases h3 : fracF f x = 0
      · rw [if_pos h3]; cases signF f x <;> simp [h1, h2, h3, hw0, Ne.symm hw0] <;> omega
      · rw [if_neg h3]; cases signF f x <;> simp [h1, h2, h3, hw0, Ne.symm hw0] <;> omega
    · rw [if_neg h2]; cases signF f x <;> simp [h1, h2, hw0, Ne.symm hw0] <;> omega

/-- §5.7.2 `isSignMinus` is the sign bit, the most significant bit of the `k`-bit string. -/
theorem isSignMinus_eq (f : Format) (x : BitVec f.k) : isSignMinus f x = x.msb := signF_eq f x

end LeanModels.SoftFloat.Binary
