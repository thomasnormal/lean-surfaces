/-
# SoftFloat, layer 2 — the CORRECTNESS theorems

The INTERPRETER HALF.  These are the only statements in the component that
mention core's operations; `LeanModels/SoftFloat/Basic.lean` is the spec half
and survives a definition swap (`docs/statement-cookbook.md` §6).

Every theorem is stated over a general `Float.Model.Format`, or over none at
all where the fact does not depend on one — `docs/family-architecture.md`
§3.5.1 clause (2).  The `binary16`/`binary32`/`binary64`/`binary128` lines are
INSTANCE COROLLARIES and base cases, never the deliverable (§0.1 II(a)).
-/
import LeanModels.SoftFloat.Basic

namespace LeanModels.SoftFloat

open Float.Model
open Float.Model.UnpackedFloat (Sign ExtendedMantissa Accuracy)

/-! ## Working lemma: the extended-mantissa shift IS division by a power of two -/

theorem em_shift_mantissa (em : ExtendedMantissa) (n : Nat) :
    (em >>> n).mantissa = em.mantissa / 2 ^ n := by
  induction n generalizing em with
  | zero => simp [HShiftRight.hShiftRight, Nat.repeat]
  | succ n ih =>
    show (Nat.repeat ExtendedMantissa.shiftRightOne (n + 1) em).mantissa = _
    rw [Nat.repeat]
    show (Nat.repeat ExtendedMantissa.shiftRightOne n em).shiftRightOne.mantissa = _
    show (Nat.repeat ExtendedMantissa.shiftRightOne n em).mantissa / 2 = _
    rw [show (Nat.repeat ExtendedMantissa.shiftRightOne n em).mantissa = (em >>> n).mantissa from rfl,
      ih, Nat.div_div_eq_div_mul, ← Nat.pow_succ]



/-! ## The BRIDGE to exact residue arithmetic

`RoundWithAccuracyIsNearest` (`Mul.lean`) bottoms out here.  Core decides every
rounding from two bits — round and sticky — and these two lemmas say what those
bits MEAN in exact arithmetic: after shifting right by `n+1`, the round bit is
bit `n` of the significand and the sticky bit records whether anything below it
survives.  Together they determine `m % 2^(n+1)` against `2^n`, which is exactly
the comparison every IEEE §4.3 mode needs.

`em_shift_round` needs no induction — one unfold plus `em_shift_mantissa`.
`em_shift_sticky` is a genuine recursion (`sticky(n+1) = round(n) ∨ sticky(n)`)
and turns on `Nat.mod_pow_succ`, with the bit CASED so that `2^n * bit` becomes
linear and `omega` can see it.
-/

/-- THE ROUND BIT after `n+1` shifts is bit `n` of `m`. -/
theorem em_shift_round (m n : Nat) :
    ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> (n + 1)).roundBit = ((m / 2 ^ n) % 2 != 0) := by
  simp only [HShiftRight.hShiftRight, Nat.repeat, ExtendedMantissa.shiftRightOne]
  rw [show (Nat.repeat ExtendedMantissa.shiftRightOne n ((ExtendedMantissa.ofMantissaAndAccuracy m .exact))).mantissa
        = ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> n).mantissa from rfl, em_shift_mantissa]
  rfl

/-- THE STICKY BIT after `n+1` shifts records whether ANY of bits `0..n-1` is set. -/
theorem em_shift_sticky (m n : Nat) :
    ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> (n + 1)).stickyBit = (m % 2 ^ n != 0) := by
  induction n with
  | zero =>
    simp [HShiftRight.hShiftRight, Nat.repeat, ExtendedMantissa.shiftRightOne,
          ExtendedMantissa.ofMantissaAndAccuracy, Nat.pow_zero, Nat.mod_one]
  | succ n ih =>
    simp only [HShiftRight.hShiftRight, Nat.repeat, ExtendedMantissa.shiftRightOne] at ih ⊢
    rw [show (Nat.repeat ExtendedMantissa.shiftRightOne n ((ExtendedMantissa.ofMantissaAndAccuracy m .exact))).mantissa
          = ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> n).mantissa from rfl, em_shift_mantissa] at *
    rw [ih]
    have h : m % 2 ^ (n + 1) = m % 2 ^ n + 2 ^ n * ((m / 2 ^ n) % 2) := Nat.mod_pow_succ
    have hp : 0 < 2 ^ n := Nat.two_pow_pos n
    -- CASE ON THE BIT, so `2 ^ n * bit` becomes LINEAR and omega can see it.
    rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ n) with hb | hb
    · -- bit is 0: the round bit contributes nothing, and h collapses
      rw [hb] at h
      simp only [ExtendedMantissa.ofMantissaAndAccuracy, hb, Nat.mul_zero, Nat.add_zero] at h ⊢
      simp [h]
    · -- bit is 1: the round bit forces sticky true, and h shows the residue is ≥ 2^n
      rw [hb] at h
      simp only [ExtendedMantissa.ofMantissaAndAccuracy, hb, Nat.mul_one] at h ⊢
      simp [h]

/-! ## The shifted extended mantissa as an explicit triple, and what core's
    rounding DOES with it. -/

theorem em_shift_eq (m n : Nat) :
    ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> (n + 1))
      = { mantissa := m / 2 ^ (n + 1),
          roundBit := (m / 2 ^ n) % 2 != 0,
          stickyBit := m % 2 ^ n != 0 } := by
  have h1 : ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> (n + 1)).mantissa = m / 2 ^ (n + 1) := by
    rw [em_shift_mantissa]; rfl
  have h2 := em_shift_round m n
  have h3 := em_shift_sticky m n
  cases hc : ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> (n + 1)) with
  | mk a b c => rw [hc] at h1 h2 h3; simp_all

/-! ## THE NEARER-NEIGHBOUR CASE ANALYSIS

Core's `roundedMantissa` IS round-half-to-even of `m / 2^(n+1)`.  Stated
against the RESIDUE, so both sides are exact integer arithmetic.
-/
theorem roundedMantissa_eq_roundHalfEven (m n : Nat) :
    ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> (n + 1)).roundedMantissa
      = (if 2 * (m % 2 ^ (n + 1)) < 2 ^ (n + 1) then m / 2 ^ (n + 1)
         else if 2 ^ (n + 1) < 2 * (m % 2 ^ (n + 1)) then m / 2 ^ (n + 1) + 1
         else m / 2 ^ (n + 1) + (m / 2 ^ (n + 1)) % 2) := by
  rw [em_shift_eq]
  have hpow : (2 : Nat) ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
  -- state the residue OVER THE SAME POWER the goal will carry, or it never fires
  have hres : m % (2 * 2 ^ n) = m % 2 ^ n + 2 ^ n * ((m / 2 ^ n) % 2) := by
    rw [← hpow]; exact Nat.mod_pow_succ
  have hlt : m % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
  rw [hpow]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ n) with hb | hb
  · rw [hb] at hres ⊢
    simp only [Nat.mul_zero, Nat.add_zero] at hres
    by_cases hs : m % 2 ^ n = 0
    · -- EXACT: nothing at or below the cut
      rw [hs] at hres
      simp [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
            Accuracy.roundToNearestEven, hs, hres]
    · -- STRICTLY BELOW half: round down
      rw [show (m % 2 ^ n != 0) = true from by simp [hs]]
      simp [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
            Accuracy.roundToNearestEven, hres]
      omega
  · rw [hb] at hres ⊢
    simp only [Nat.mul_one] at hres
    by_cases hs : m % 2 ^ n = 0
    · -- EXACTLY half: the TIE, resolved to even
      rw [hs] at hres
      simp only [Nat.zero_add] at hres
      rw [show (m % 2 ^ n != 0) = false from by simp [hs]]
      simp [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
            Accuracy.roundToNearestEven, hres]
    · -- STRICTLY ABOVE half: round up
      rw [show (m % 2 ^ n != 0) = true from by simp [hs]]
      simp [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
            Accuracy.roundToNearestEven, hres]
      -- `omega` cannot resolve an `if`; discharge both conditions first.
      rw [if_neg (by omega), if_pos (by omega)]

/-! ## CARRY-OUT ABSORPTION

`roundWithAccuracy` shifts a SECOND time after rounding, for one reason: rounding
up can carry the significand past `2 ^ mantissaBits`.  The obligation is that
this second shift changes the REPRESENTATION and not the VALUE. -/

/-- The second shift's exponent is the first plus the shift amount — by `rfl`. -/
theorem shiftToExponent_exp (m : Nat) (e t : Int) (a : Accuracy) :
    (UnpackedFloat.shiftToExponent m e a t).2 = e + ((t - e).toNat : Int) := rfl

/-- Its mantissa is the input divided by the shift. -/
theorem shiftToExponent_mantissa (m : Nat) (e t : Int) (a : Accuracy) :
    (UnpackedFloat.shiftToExponent m e a t).1.mantissa = m / 2 ^ (t - e).toNat := by
  show ((ExtendedMantissa.ofMantissaAndAccuracy m a) >>> (t - e).toNat).mantissa = _
  rw [em_shift_mantissa]
  -- `ofMantissaAndAccuracy` matches THREE `.inexact` sub-patterns, so `cases a`
  -- alone leaves the ordering symbolic and the match stuck.
  rcases a with _ | o
  · rfl
  · cases o <;> rfl

/--
**VALUE PRESERVATION.**  When the bits the shift drops are zero, the shift is
exact: significand × 2^shift recovers the input.  This is what makes the
carry-out absorption sound — it re-expresses the same number, it does not
approximate it.
-/
theorem shiftToExponent_exact (m : Nat) (e t : Int) (a : Accuracy)
    (h : m % 2 ^ (t - e).toNat = 0) :
    (UnpackedFloat.shiftToExponent m e a t).1.mantissa * 2 ^ (t - e).toNat = m := by
  rw [shiftToExponent_mantissa]
  exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)

/--
**THE CARRY CASE ITSELF.**  A significand that rounding carried to exactly
`2 ^ k` (`k > 0`) is even, so the one-place shift the carry triggers is exact
and the value survives: the second shift re-expresses the number, it does not
approximate it.
-/
theorem carry_shift_exact (k : Nat) (hk : 0 < k) (e t : Int)
    (ht : (t - e).toNat = 1) (a : Accuracy) :
    (UnpackedFloat.shiftToExponent (2 ^ k) e a t).1.mantissa * 2 = 2 ^ k := by
  have heven : (2 : Nat) ^ k % 2 = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.pow_succ]; omega
  have h : (2 : Nat) ^ k % 2 ^ (t - e).toNat = 0 := by rw [ht, Nat.pow_one]; exact heven
  have hx := shiftToExponent_exact (2 ^ k) e t a h
  rwa [ht, Nat.pow_one] at hx

/-! ## THE ES ROW: core's float→int conversion IS truncation of the exact value

IEEE 754-2019 §5.8 `convertToIntegerTowardZero`.  The statement mentions NO
`Format`: truncation does not depend on the format, so §3.5.1 clause 2 is
satisfied a fortiori rather than narrowly.
-/

theorem roundToInt_eq_truncate (s : Sign) (m : Nat) (e : Int) :
    UnpackedFloat.roundToInt s m e = (Q.dyadic (s.apply (m : Int)) e).truncate := by
  unfold UnpackedFloat.roundToInt UnpackedFloat.decreaseExponent UnpackedFloat.shiftToExponent
  simp only []
  rcases Int.lt_or_le e 0 with he | he
  · rw [show (e - 0).toNat = 0 by omega]
    simp only [Nat.shiftLeft_zero]
    rw [show (0 - (e - ((0 : Nat) : Int))).toNat = (-e).toNat by omega]
    rw [em_shift_mantissa]
    unfold Q.dyadic Q.truncate UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
    rw [if_neg (by omega)]
    cases s <;> simp [Sign.apply, Int.neg_tdiv]
  · rw [show (e - 0).toNat = e.toNat by omega]
    rw [show (0 - (e - ((e.toNat : Nat) : Int))).toNat = 0 by omega]
    rw [em_shift_mantissa]
    unfold Q.dyadic Q.truncate UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
    rw [if_pos he]
    cases s <;> simp [Sign.apply, Nat.shiftLeft_eq, Int.neg_mul]

/--
Core's `UnpackedFloat.toInt` is exactly truncation-toward-zero of the exact
value, for every float that HAS an exact value.  The infinities and NaN are
excluded by the hypothesis rather than by a side condition, which is what makes
this the specification's statement and not the algorithm's.
-/
theorem toInt_eq_truncate {lo hi : Int} {x : UnpackedFloat} {q : Q}
    (h : valQ x = some q) : UnpackedFloat.toInt lo hi x = q.truncate := by
  cases x with
  | notANumber => simp [valQ] at h
  | infinity s => simp [valQ] at h
  | zero s =>
    simp only [valQ, Option.some.injEq] at h
    subst h; rfl
  | finite s m e hm =>
    simp only [valQ, Option.some.injEq] at h
    subst h; exact roundToInt_eq_truncate s m e

/-! ## The IEEE special-value rows, over a GENERAL `Format` (§0.1 II(a) rung 1) -/

/-- IEEE 754-2019 §6.2: NaN propagates through addition, in EVERY format. -/
theorem add_nan_left (fmt : Format) (x : UnpackedFloat) :
    UnpackedFloat.add fmt .notANumber x = .notANumber := rfl

/-- IEEE 754-2019 §6.3: `(+0) + (-0)` is `+0` under roundTiesToEven, EVERY format. -/
theorem add_zero_opposite_signs (fmt : Format) :
    UnpackedFloat.add fmt (.zero .positive) (.zero .negative) = .zero .positive := rfl

/-- IEEE 754-2019 §6.3: adding two zeros of the same sign preserves it, EVERY format. -/
theorem add_zero_same_sign (fmt : Format) (s : Sign) :
    UnpackedFloat.add fmt (.zero s) (.zero s) = .zero s := by cases s <;> rfl

/-- IEEE 754-2019 §7.2: `(+∞) + (−∞)` is invalid, hence NaN, in EVERY format. -/
theorem add_inf_opposite (fmt : Format) :
    UnpackedFloat.add fmt (.infinity .positive) (.infinity .negative) = .notANumber := rfl

/-- IEEE 754-2019 §7.2: `0 / 0` is invalid, hence NaN, in EVERY format. -/
theorem div_zero_zero (fmt : Format) (s₁ s₂ : Sign) :
    UnpackedFloat.div fmt (.zero s₁) (.zero s₂) = .notANumber := by cases s₁ <;> cases s₂ <;> rfl

/-- IEEE 754-2019 §7.3: a finite nonzero over zero is a signed infinity, EVERY format. -/
theorem div_by_zero (fmt : Format) (s₁ s₂ : Sign) (m : Nat) (e : Int) (hm : 0 < m) :
    UnpackedFloat.div fmt (.finite s₁ m e hm) (.zero s₂) = .infinity (s₁ / s₂) := rfl

/-- IEEE 754-2019 §5.11: NaN is unordered with everything. -/
theorem compare_nan (x : UnpackedFloat) :
    UnpackedFloat.compare .notANumber x = none := rfl

/-- IEEE 754-2019 §5.11: `+0` and `−0` compare equal. -/
theorem compare_zeros (s₁ s₂ : Sign) :
    UnpackedFloat.compare (.zero s₁) (.zero s₂) = some .eq := by cases s₁ <;> cases s₂ <;> rfl

/-- IEEE 754-2019 §7.2: `√` of a negative finite is invalid, hence NaN, EVERY format. -/
theorem sqrt_neg (fmt : Format) (m : Nat) (e : Int) (hm : 0 < m) :
    UnpackedFloat.sqrt fmt (.finite .negative m e hm) = .notANumber := rfl

/-! ## Instance corollaries — `decide`-closed BASE CASES, never the deliverable -/

/-- IEEE 754-2019 §3.6 binary16, as an INSTANCE of the general `Format`. -/
abbrev binary16  : Format := { mantissaBitsWithoutImplicit := 10,  exponentBits := 5 }
/-- IEEE 754-2019 §3.6 binary128, as an INSTANCE of the general `Format`. -/
abbrev binary128 : Format := { mantissaBitsWithoutImplicit := 112, exponentBits := 15 }

example : UnpackedFloat.add binary16 .notANumber (.zero .positive) = .notANumber :=
  add_nan_left binary16 _
example : UnpackedFloat.add Format.binary32 .notANumber (.zero .positive) = .notANumber :=
  add_nan_left Format.binary32 _
example : UnpackedFloat.add Format.binary64 .notANumber (.zero .positive) = .notANumber :=
  add_nan_left Format.binary64 _
example : UnpackedFloat.add binary128 .notANumber (.zero .positive) = .notANumber :=
  add_nan_left binary128 _

/-! ## RUN, not admired: the consumers' own rows, instantiated

TWO ORACLES, AND THEY ARE NOT THE SAME ORACLE.  `#guard` runs the UNTRUSTED
evaluator — core says so itself (`Init/Guard.lean`: *"this uses the untrusted
evaluator, so `#guard` passing is not a proof that the expression equals
`true`"*), and `Lean/Elab/Tactic/Guard.lean` calls `unsafe evalExpr`.  So a
`#guard` CANNOT gate kernel reduction: it passes identically whether the
declaration reduces or is `opaque` — measured, twice, in this lane's probes.

What the pair is good for is a DIFFERENTIAL: `#guard` attests the compiled C
runtime, `rfl`/`decide` attest core's logical model, and a row carrying both
has checked the two against each other.  Every row below carries both.
-/

-- ES (ECMA-262 §7.1.5 `ToIntegerOrInfinity` truncates toward zero), routed
-- through the MODEL rather than through `Float.toInt64`, which core's own
-- docstring says "does not reduce in the kernel".
#guard (2.75 : Float).toModel.toInt64 = (2 : Int64)          -- C runtime
example : (2.75 : Float).toModel.toInt64 = (2 : Int64) := by decide   -- kernel
#guard (-2.75 : Float).toModel.toInt64 = (-2 : Int64)
example : (-2.75 : Float).toModel.toInt64 = (-2 : Int64) := by decide

-- and the theorem instantiated on those rows:
example : UnpackedFloat.toInt 0 0 (.finite .positive 11 (-2) (by decide))
        = (Q.dyadic 11 (-2)).truncate := toInt_eq_truncate rfl

-- SV (the divider flagship's row): 1/8 is exact in every binary format.
-- Both oracles on the binary32 row; the kernel oracle alone on binary16.
example : UnpackedFloat.pack binary16
        (UnpackedFloat.div binary16
          (UnpackedFloat.ofNat binary16 1) (UnpackedFloat.ofNat binary16 8))
     = UnpackedFloat.pack binary16 (UnpackedFloat.ofScientific binary16 125 (-3)) := by decide
#guard UnpackedFloat.pack Format.binary32
        (UnpackedFloat.div Format.binary32
          (UnpackedFloat.ofNat Format.binary32 1) (UnpackedFloat.ofNat Format.binary32 8))
     = UnpackedFloat.pack Format.binary32 (UnpackedFloat.ofScientific Format.binary32 125 (-3))
#guard UnpackedFloat.pack binary16
        (UnpackedFloat.div binary16
          (UnpackedFloat.ofNat binary16 1) (UnpackedFloat.ofNat binary16 8))
     = UnpackedFloat.pack binary16 (UnpackedFloat.ofScientific binary16 125 (-3))

#print axioms em_shift_mantissa
#print axioms roundToInt_eq_truncate
#print axioms toInt_eq_truncate
#print axioms add_nan_left
#print axioms add_zero_opposite_signs
#print axioms add_zero_same_sign
#print axioms add_inf_opposite
#print axioms div_zero_zero
#print axioms div_by_zero
#print axioms compare_nan
#print axioms compare_zeros
#print axioms sqrt_neg

end LeanModels.SoftFloat
