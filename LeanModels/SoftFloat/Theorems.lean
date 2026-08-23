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
open Float.Model.UnpackedFloat (Sign ExtendedMantissa)

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
