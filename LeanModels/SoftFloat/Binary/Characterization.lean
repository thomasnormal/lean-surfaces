import LeanModels.SoftFloat.Binary.Divide

/-!
# Division is characterized by §4.3.1, §6.3 and §7.2, independently of `round`

Five properties of `divide` stated with bit patterns, `decode`, exact fractions and integer inequalities only, and
proved for every format:

* `divide_isNearestTiesToEven` — a quotient that has a value is a nearest number of the format to `x / y`, and on a
  tie its last bit is 0 (§4.3.1);
* `divide_overflowsAtThreshold` — the quotient is an infinity exactly when `|x / y| ≥ 2^emax × (2 − 2^(−p))`
  (§4.3.1, §7.4);
* `divide_ofNumbersIsNotNaN` — under every attribute, a quotient of two numbers with a nonzero divisor is an
  infinity or has a value (§7.2);
* `divide_signIsXor` — every non-NaN quotient has the XOR of the operands' sign bits (§6.3);
* `divide_isUniquelyCharacterized` — any pattern with the four properties above is the roundTiesToEven quotient,
  so they are a complete specification on operands that are numbers with a nonzero divisor.

They are the evidence that `divide` (hence `round`) says what the standard says. The file ends with `divide_isResult`:
`divide` meets `DivisionResult`, the IEEE-level specification that admits every quiet NaN. svGolf's fdivp statement states the
same five propositions of its own definitions; `tests/fdivp/Characterization.lean` there derives them from these.

Ported from svGolf's fdivp reference proof (section `IEEE754Proofs`) and the propositions of its trusted
`tasks/fdivp/IEEE754.lean`, the maintainers' text.
-/

namespace LeanModels.SoftFloat.Binary

open NatFacts

/-! ## Characterization (statements)

The first four propositions below restate what IEEE 754-2019 requires of `division` directly
in terms of bit patterns, `decode`, exact fractions and integer inequalities, independently of
how `round` computes; the fifth says that those four leave only one possible result.
They are proved below for every format `f`. Fractions are pairs
`(num, den) : Int × Nat` with `den > 0`, as in `Datum.value?`.

* `DivideIsNearestTiesToEven` — a quotient that has a value is a nearest number, ties to even;
* `DivideOverflowsAtThreshold` — a quotient is an infinity exactly at the overflow threshold;
* `DivideOfNumbersIsNotNaN` — a quotient of two numbers (nonzero divisor) is never a NaN, so
  it is always covered by one of the two statements above;
* `DivideSignIsXor` — every non-NaN quotient has the XOR sign, zeros and infinities included;
* `DivideIsUniquelyCharacterized` — any bit pattern with the four properties above is the
  roundTiesToEven quotient.

How they fit together is spelled out before the last one. -/

/-- `NoFarther a b x`: the fraction `a = a.1 / a.2` is at least as close to `x` as `b` is,
`|a − x| ≤ |b − x|`, stated by cross-multiplication (all denominators positive):
`|a.1·x.2 − x.1·a.2| / (a.2·x.2) ≤ |b.1·x.2 − x.1·b.2| / (b.2·x.2)`. -/
def NoFarther (a b x : Int × Nat) : Prop :=
  (a.1 * x.2 - x.1 * a.2).natAbs * b.2 ≤ (b.1 * x.2 - x.1 * b.2).natAbs * a.2

/-- The exact quotient `x / y` of two fractions with `y ≠ 0`, with a positive denominator:
`(x.1/x.2) / (y.1/y.2) = (x.1·y.2) / (x.2·y.1)`, the sign moved to the numerator. -/
def fracDiv (x y : Int × Nat) : Int × Nat :=
  (if y.1 < 0 then -(x.1 * y.2) else x.1 * y.2, x.2 * y.1.natAbs)

/-- **`divide` under roundTiesToEven delivers the nearest number, ties to even** (§4.3.1,
§5.4.1). Let `a`, `b` be bit patterns whose exact values `x`, `y` exist (zero or finite
operands) with `y ≠ 0`, and suppose their quotient `divide f .nearestTiesToEven a b` is zero or
finite with exact value `r`. (Read alone, this hypothesis excludes NaN results as well as
infinities, so it would leave a NaN result unconstrained; `DivideOfNumbersIsNotNaN` shows there
is none. With `DivideOverflowsAtThreshold`, the hypothesis therefore holds exactly for the
quotients below the overflow threshold.) Then:

1. *nearest* — every finite number (or zero) `v` of the format is at least as far from the
   exact quotient `x / y` as `r` is;
2. *ties to even* — if a finite number `v` with a different value is no farther from `x / y`
   than `r` (so the two are equally near), then the delivered bit pattern has least
   significant bit 0: its significand's last digit is even. -/
def DivideIsNearestTiesToEven (f : Format) : Prop :=
  ∀ (a b : BitVec f.k) (x y r : Int × Nat),
    (decode f a).value? = some x → (decode f b).value? = some y → y.1 ≠ 0 →
    (decode f (divide f .nearestTiesToEven a b)).value? = some r →
      (∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
          NoFarther r v (fracDiv x y)) ∧
      (∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
          v.1 * r.2 ≠ r.1 * v.2 → NoFarther v r (fracDiv x y) →
          (divide f .nearestTiesToEven a b).toNat % 2 = 0)

/-- **Overflow happens exactly at the §4.3.1 threshold** ("an infinitely precise result with
magnitude at least `b^emax × (b − ½ b^(1−p))` shall round to `∞` with no change in sign"; §7.4).
For bit patterns `a`, `b` whose exact values `x`, `y` exist with `y ≠ 0`, the roundTiesToEven
quotient is an infinity iff `|x / y| ≥ 2^emax × (2 − 2^(−p))`; writing `x / y = n / d`
(`fracDiv`) this is the integer inequality `d × 2^emax × (2^(p+1) − 1) ≤ |n| × 2^p`.
On its own this says nothing about a quotient below the threshold beyond "not an infinity";
`DivideOfNumbersIsNotNaN` adds that such a quotient has a value, so that
`DivideIsNearestTiesToEven` applies to it. -/
def DivideOverflowsAtThreshold (f : Format) : Prop :=
  ∀ (a b : BitVec f.k) (x y : Int × Nat),
    (decode f a).value? = some x → (decode f b).value? = some y → y.1 ≠ 0 →
    ((∃ s, decode f (divide f .nearestTiesToEven a b) = .inf s) ↔
      (fracDiv x y).2 * 2 ^ f.emax * (2 ^ (f.p + 1) - 1) ≤ (fracDiv x y).1.natAbs * 2 ^ f.p)

/-- **A quotient of two numbers is never a NaN** (§7.2: the invalid divisions are
`division(0, 0)` and `division(∞, ∞)`, and neither has two numbers with a nonzero divisor). For
bit patterns `a`, `b` whose exact values `x`, `y` exist (zero or finite operands) with `y ≠ 0`,
the quotient under **every** rounding-direction attribute is an infinity or has an exact value
(a zero or a finite number).

The conclusion is exactly the union of the cases the other statements speak about: infinities
(`DivideOverflowsAtThreshold`) and results with a value (`DivideIsNearestTiesToEven`). Without
it, those two would also be satisfied by a divider that returned a NaN for every quotient below
the overflow threshold. -/
def DivideOfNumbersIsNotNaN (f : Format) : Prop :=
  ∀ (mode : RoundingMode) (a b : BitVec f.k) (x y : Int × Nat),
    (decode f a).value? = some x → (decode f b).value? = some y → y.1 ≠ 0 →
    (∃ s, decode f (divide f mode a b) = .inf s) ∨
      ∃ r, (decode f (divide f mode a b)).value? = some r

/-- **The sign of a quotient is the exclusive OR of the operands' signs** (§6.3: "When neither
the inputs nor result are NaN, the sign of a product or quotient is the exclusive OR of the
operands' signs"), for **every** pair of bit patterns and every rounding-direction attribute,
zero, infinite and overflowed results included. `BitVec.msb` is the most significant bit of
the `k`-bit string: the sign bit `S` (§3.4). The hypothesis is only that the *result* is not a
NaN; NaN operands always give a NaN result here, so this is the clause's condition. -/
def DivideSignIsXor (f : Format) : Prop :=
  ∀ (mode : RoundingMode) (a b : BitVec f.k),
    (∀ s, decode f (divide f mode a b) ≠ .nan s) →
      (divide f mode a b).msb = (a.msb ^^ b.msb)

/-! ### How the statements fit together

Take bit patterns `a`, `b` with exact values `x`, `y` and `y ≠ 0`, and let
`R = divide f .nearestTiesToEven a b`. Then:

1. `R` is not a NaN: it is an infinity or has a value (`DivideOfNumbersIsNotNaN`);
2. its sign bit is `a.msb ^^ b.msb` (`DivideSignIsXor`);
3. it is an infinity exactly when `|x / y|` reaches the threshold (`DivideOverflowsAtThreshold`);
4. otherwise its value is a nearest number of the format to `x / y`, and on a tie its last bit
   is 0 (`DivideIsNearestTiesToEven`).

These four properties leave exactly one possible bit pattern, and that is proved too:
`DivideIsUniquelyCharacterized` below states that any pattern `R` with properties 1–4 is
`divide f .nearestTiesToEven a b`. So for these operands a reader can take properties 1–4 as the
specification and need not read `round` at all. (Informally: above the threshold the result is
the infinity with the XOR sign. Below it, two different patterns with the same sign bit cannot
both qualify. Their values would be distinct and equally near `x / y`, so they would be adjacent
numbers of the format, both ending in bit 0. But adjacent numbers of one sign have consecutive
encodings, so their last bits differ.)

All other operand pairs, namely a NaN or infinite operand or a zero divisor, are the
special-case table in `divide` itself, which is meant to be read directly. The signs of its
non-NaN results are also covered by `DivideSignIsXor`. -/

/-- **Properties 1–4 determine the roundTiesToEven quotient.** For bit patterns `a`, `b` whose
exact values `x`, `y` exist with `y ≠ 0`, any bit pattern `R` that has the four properties that
`DivideOfNumbersIsNotNaN`, `DivideSignIsXor`, `DivideOverflowsAtThreshold` and
`DivideIsNearestTiesToEven` state of `divide f .nearestTiesToEven a b` (copied here verbatim with
`R` in its place) is equal to `divide f .nearestTiesToEven a b`. -/
def DivideIsUniquelyCharacterized (f : Format) : Prop :=
  ∀ (a b R : BitVec f.k) (x y : Int × Nat),
    (decode f a).value? = some x → (decode f b).value? = some y → y.1 ≠ 0 →
    -- 1. not a NaN
    ((∃ s, decode f R = .inf s) ∨ ∃ r, (decode f R).value? = some r) →
    -- 2. the XOR sign
    ((∀ s, decode f R ≠ .nan s) → R.msb = (a.msb ^^ b.msb)) →
    -- 3. an infinity exactly at the threshold
    ((∃ s, decode f R = .inf s) ↔
      (fracDiv x y).2 * 2 ^ f.emax * (2 ^ (f.p + 1) - 1) ≤ (fracDiv x y).1.natAbs * 2 ^ f.p) →
    -- 4. otherwise nearest, ties to even
    (∀ r, (decode f R).value? = some r →
      (∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
          NoFarther r v (fracDiv x y)) ∧
      (∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
          v.1 * r.2 ≠ r.1 * v.2 → NoFarther v r (fracDiv x y) → R.toNat % 2 = 0)) →
    R = divide f .nearestTiesToEven a b

theorem decode_fields (f : Format) (neg : Bool) (E T : Nat) (hE : E < 2 ^ f.w)
    (hT : T < 2 ^ f.t) :
    decode f (fields f neg E T) =
      if E = 2 ^ f.w - 1 then (if T = 0 then .inf neg else .nan (T < 2 ^ (f.t - 1)))
      else if E = 0 then (if T = 0 then .zero neg else .finite neg (f.emin - f.t) T)
      else .finite neg ((E : Int) - f.emax - f.t) (2 ^ f.t + T) := by
  have hlow : E * 2 ^ f.t + T < 2 ^ (f.w + f.t) := by
    rw [Nat.pow_add]
    have : (E + 1) * 2 ^ f.t ≤ 2 ^ f.w * 2 ^ f.t := Nat.mul_le_mul_right _ hE
    rw [Nat.succ_mul] at this; omega
  have ht := Nat.two_pow_pos f.t
  have h1 : (fields f neg E T).toNat / 2 ^ (f.w + f.t) = if neg then 1 else 0 := by
    rw [fields_toNat f neg E T hE hT, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hlow, Nat.zero_add]
  have h2 : (fields f neg E T).toNat / 2 ^ f.t % 2 ^ f.w = E := by
    rw [fields_toNat f neg E T hE hT, Nat.pow_add, ← Nat.mul_assoc, Nat.add_comm,
      Nat.add_mul_div_right _ _ ht, Nat.add_comm (E * _), Nat.add_mul_div_right _ _ ht,
      Nat.div_eq_of_lt hT, Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hE]
  have h3 : (fields f neg E T).toNat % 2 ^ f.t = T := by
    rw [fields_toNat f neg E T hE hT, Nat.pow_add, ← Nat.mul_assoc, Nat.add_comm,
      Nat.add_mul_mod_self_right, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hT]
  unfold decode
  simp only [h1, h2, h3]
  have : ((if neg = true then 1 else 0) == 1) = neg := by cases neg <;> rfl
  rw [this]

theorem scale_eq (f : Format) : (f.scale : Int) = -f.qmin := by
  have := emax_pos f
  unfold Format.scale Format.qmin Format.emin
  omega

/-- `v` is the exact value `(−1)^neg × u × 2^qmin = ±u / 2^scale` as a fraction. -/
def IsUnits (f : Format) (v : Int × Nat) (neg : Bool) (u : Nat) : Prop :=
  0 < v.2 ∧ v.1 * 2 ^ f.scale = (if neg then -(u : Int) else u) * v.2

/-- `n` with sign `neg`: `(−1)^neg × n`. -/
def sgn (neg : Bool) (n : Nat) : Int := if neg then -(n : Int) else n

theorem value_finite (f : Format) (neg : Bool) (q : Int) (c : Nat) (hq : f.qmin ≤ q) :
    ∃ v, (Datum.finite neg q c).value? = some v ∧
      IsUnits f v neg (c * 2 ^ (q - f.qmin).toNat) := by
  refine ⟨_, rfl, Nat.two_pow_pos _, ?_⟩
  have hS := scale_eq f
  have e : q.toNat + f.scale = (q - f.qmin).toNat + (-q).toNat := by omega
  have e2 : (2 : Int) ^ q.toNat * 2 ^ f.scale = 2 ^ (q - f.qmin).toNat * 2 ^ (-q).toNat := by
    rw [← Int.pow_add, ← Int.pow_add, e]
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.natCast_mul, Int.natCast_pow,
    Int.cast_ofNat_Int, Int.neg_mul, Int.mul_assoc, e2]

theorem value_zero (f : Format) (neg : Bool) :
    ∃ v, (Datum.zero neg).value? = some v ∧ IsUnits f v neg 0 :=
  ⟨_, rfl, by decide, by simp⟩

/-- Every finite datum decoded from a bit pattern has `0 < c < 2^p` and `qmin ≤ q`. -/
theorem decode_finite_bounds (f : Format) (z : BitVec f.k) (neg : Bool) (q : Int) (c : Nat)
    (h : decode f z = .finite neg q c) : c < 2 ^ f.p ∧ f.qmin ≤ q := by
  have hp := f.hp
  have ht : 2 ^ f.t + 2 ^ f.t = 2 ^ f.p := by
    rw [← Nat.two_mul, ← Nat.pow_succ']; congr 1; simp only [Format.t]; omega
  have hT := Nat.mod_lt z.toNat (Nat.two_pow_pos f.t)
  unfold decode at h
  simp only at h
  split at h
  · split at h <;> cases h
  · split at h
    · split at h
      · cases h
      · cases h; exact ⟨by omega, Int.le_refl _⟩
    · cases h
      refine ⟨by omega, ?_⟩
      unfold Format.qmin Format.emin; omega

/-- Every zero or finite pattern's value is `±u` units for a representable `u`. -/
theorem value_decode (f : Format) (z : BitVec f.k) (v : Int × Nat)
    (h : (decode f z).value? = some v) : ∃ neg u, RepU f u ∧ IsUnits f v neg u := by
  cases hd : decode f z with
  | nan _ => rw [hd] at h; cases h
  | inf _ => rw [hd] at h; cases h
  | zero neg =>
    rw [hd] at h; cases h
    exact ⟨neg, 0, ⟨0, 0, Nat.two_pow_pos _, rfl⟩, by decide, by simp⟩
  | finite neg q c =>
    obtain ⟨hc, hq⟩ := decode_finite_bounds f z neg q c hd
    obtain ⟨v', hv', hu⟩ := value_finite f neg q c hq
    rw [hd, hv'] at h; cases h
    exact ⟨neg, _, ⟨c, _, hc, rfl⟩, hu⟩

theorem decode_encode (f : Format) (neg : Bool) (u : Nat) (hu : RepU f u)
    (hmax : u ≤ f.maxUnits) :
    ∃ v, (decode f (finite f neg u)).value? = some v ∧ IsUnits f v neg u := by
  have hp := f.hp
  have hw2 := two_emax f
  have h4 : 4 ≤ 2 ^ f.w := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ f.w := Nat.pow_le_pow_right (by omega) f.hw
  unfold finite
  by_cases hlt : u < 2 ^ f.t
  · rw [if_pos hlt, decode_fields f neg 0 u (Nat.two_pow_pos _) hlt,
      if_neg (by omega), if_pos rfl]
    by_cases h0 : u = 0
    · subst h0; exact ⟨_, rfl, by decide, by simp⟩
    · rw [if_neg h0]
      obtain ⟨v, hv, hU⟩ := value_finite f neg (f.emin - f.t) u (Int.le_refl _)
      refine ⟨v, hv, ?_⟩
      have : (f.emin - f.t - f.qmin).toNat = 0 := by unfold Format.qmin; omega
      rwa [this, Nat.pow_zero, Nat.mul_one] at hU
  · rw [if_neg hlt]
    simp only []
    have hu0 : u ≠ 0 := by have := Nat.two_pow_pos f.t; omega
    obtain ⟨hlo, hT, hj2⟩ := normal_bounds f u hmax (by omega)
    generalize hj : Nat.log2 u - f.t = j at hlo hT hj2
    rw [decode_fields f neg (j + 1) (u / 2 ^ j - 2 ^ f.t) (by omega) hT,
      if_neg (by omega), if_neg (by omega)]
    have hq : f.qmin ≤ ((j + 1 : Nat) : Int) - f.emax - f.t := by
      unfold Format.qmin Format.emin; omega
    obtain ⟨v, hv, hU⟩ := value_finite f neg _ (2 ^ f.t + (u / 2 ^ j - 2 ^ f.t)) hq
    refine ⟨v, hv, ?_⟩
    have e1 : (((j + 1 : Nat) : Int) - f.emax - f.t - f.qmin).toNat = j := by
      unfold Format.qmin Format.emin; omega
    have e2 : (2 ^ f.t + (u / 2 ^ j - 2 ^ f.t)) * 2 ^ j = u := by
      rw [Nat.add_sub_cancel' hlo, Nat.div_mul_cancel (hj ▸ rep_dvd f u hu hu0)]
    rwa [e1, e2] at hU

theorem isUnits_sgn (f : Format) (v : Int × Nat) (neg : Bool) (u : Nat) :
    IsUnits f v neg u ↔ 0 < v.2 ∧ v.1 * 2 ^ f.scale = sgn neg u * v.2 := Iff.rfl

theorem sgn_mul (s : Bool) (a b : Nat) : sgn s a * (b : Int) = sgn s (a * b) := by
  cases s <;> simp [sgn, Int.neg_mul]

theorem natAbs_sgn_same (s : Bool) (a b : Nat) :
    (sgn s a - sgn s b).natAbs = (b - a) + (a - b) := by
  cases s <;> simp only [sgn, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem natAbs_sgn_opp (s : Bool) (a b : Nat) :
    (sgn (!s) a - sgn s b).natAbs = a + b := by
  cases s <;> simp only [sgn, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] <;>
    omega

theorem value_finite_eq (neg : Bool) (q : Int) (c : Nat) :
    (Datum.finite neg q c).value? = some (sgn neg (c * 2 ^ q.toNat), 2 ^ (-q).toNat) := by
  cases neg <;> simp [Datum.value?, sgn]

theorem fracDiv_sgn (sa sb : Bool) (nx dx ny dy : Nat) (hny : ny ≠ 0) :
    fracDiv (sgn sa nx, dx) (sgn sb ny, dy) = (sgn (sa ^^ sb) (nx * dy), dx * ny) := by
  have h1 : ¬ ((ny : Int) < 0) := by omega
  have h2 : -(ny : Int) < 0 := by omega
  cases sa <;> cases sb <;>
    simp only [fracDiv, sgn, Bool.false_eq_true, ↓reduceIte, Bool.xor_false, Bool.xor_true,
      Bool.not_true, Bool.not_false, h1, h2, Int.neg_mul, Int.neg_neg, Int.natAbs_neg,
      Int.natAbs_natCast, Int.natCast_mul]

/-- Two fractions with the same signed units are equal fractions. -/
theorem eqv_of_units (f : Format) (v r : Int × Nat) (sv sr : Bool) (uv ur : Nat)
    (hv : IsUnits f v sv uv) (hr : IsUnits f r sr ur) (h : sgn sv uv = sgn sr ur) :
    v.1 * r.2 = r.1 * v.2 := by
  rw [isUnits_sgn] at hv hr
  have hP : (2 : Int) ^ f.scale ≠ 0 := Int.ne_of_gt (Int.pow_pos (by decide))
  apply Int.eq_of_mul_eq_mul_right hP
  calc v.1 * r.2 * 2 ^ f.scale = v.1 * 2 ^ f.scale * r.2 := by ac_rfl
    _ = r.1 * 2 ^ f.scale * v.2 := by rw [hv.2, hr.2, h]; ac_rfl
    _ = r.1 * v.2 * 2 ^ f.scale := by ac_rfl

/-- Comparing distances to `±Nq / Dq` of two fractions given in units: `NoFarther` is the
comparison of `|±u·Dq − ±Nq·2^scale|`. -/
theorem noFarther_iff_units (f : Format) (r v : Int × Nat) (σr σv σ : Bool) (u u' Nq Dq : Nat)
    (hr : IsUnits f r σr u) (hv : IsUnits f v σv u') :
    NoFarther r v (sgn σ Nq, Dq) ↔
      (sgn σr u * Dq - sgn σ Nq * 2 ^ f.scale).natAbs ≤
      (sgn σv u' * Dq - sgn σ Nq * 2 ^ f.scale).natAbs := by
  rw [isUnits_sgn] at hr hv
  obtain ⟨hr2, hr⟩ := hr
  obtain ⟨hv2, hv⟩ := hv
  unfold NoFarther
  simp only
  have kA : (r.1 * Dq - sgn σ Nq * r.2) * 2 ^ f.scale =
      r.2 * (sgn σr u * Dq - sgn σ Nq * 2 ^ f.scale) := by grind
  have kB : (v.1 * Dq - sgn σ Nq * v.2) * 2 ^ f.scale =
      v.2 * (sgn σv u' * Dq - sgn σ Nq * 2 ^ f.scale) := by grind
  have nA := congrArg Int.natAbs kA
  have nB := congrArg Int.natAbs kB
  simp only [Int.natAbs_mul, Int.natAbs_pow, show Int.natAbs 2 = 2 from rfl, Int.natAbs_natCast] at nA nB
  generalize (r.1 * Dq - sgn σ Nq * r.2).natAbs = A at *
  generalize (v.1 * Dq - sgn σ Nq * v.2).natAbs = B at *
  generalize (sgn σr u * Dq - sgn σ Nq * 2 ^ f.scale).natAbs = α at *
  generalize (sgn σv u' * Dq - sgn σ Nq * 2 ^ f.scale).natAbs = β at *
  have hP := Nat.two_pow_pos f.scale
  constructor
  · intro h
    have : r.2 * v.2 * α ≤ r.2 * v.2 * β := by
      have := Nat.mul_le_mul_right (2 ^ f.scale) h
      calc r.2 * v.2 * α = v.2 * (r.2 * α) := by ac_rfl
        _ = A * v.2 * 2 ^ f.scale := by rw [← nA]; ac_rfl
        _ ≤ B * r.2 * 2 ^ f.scale := this
        _ = r.2 * (v.2 * β) := by rw [← nB]; ac_rfl
        _ = r.2 * v.2 * β := by ac_rfl
    exact Nat.le_of_mul_le_mul_left this (Nat.mul_pos hr2 hv2)
  · intro h
    apply Nat.le_of_mul_le_mul_right _ hP
    calc A * v.2 * 2 ^ f.scale = v.2 * (r.2 * α) := by rw [Nat.mul_right_comm, nA]; ac_rfl
      _ ≤ v.2 * (r.2 * β) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h)
      _ = B * r.2 * 2 ^ f.scale := by rw [Nat.mul_right_comm, nB]; ac_rfl

theorem decode_infinity (f : Format) (neg : Bool) : decode f (infinity f neg) = .inf neg := by
  unfold infinity
  have := Nat.two_pow_pos f.w
  rw [decode_fields f neg (2 ^ f.w - 1) 0 (by omega) (Nat.two_pow_pos _), if_pos rfl, if_pos rfl]

/-- An encoded magnitude with even significand has least significant bit 0. -/
theorem finite_lsb (f : Format) (neg : Bool) (u : Nat) (hmax : u ≤ f.maxUnits) (he : EvenSig f u) : (finite f neg u).toNat % 2 = 0 := by
  have hp := f.hp
  have hw2 := two_emax f
  have ht2 : 2 ^ f.t = 2 * 2 ^ (f.t - 1) := by
    rw [← Nat.pow_succ']; congr 1; simp only [Format.t]; omega
  have hwt : 2 ^ (f.w + f.t) = 2 * 2 ^ (f.w + f.t - 1) := by
    rw [← Nat.pow_succ']; congr 1; simp only [Format.t]; omega
  have parity : ∀ E T, E < 2 ^ f.w → T < 2 ^ f.t → T % 2 = 0 →
      (fields f neg E T).toNat % 2 = 0 := by
    intro E T hE hT h
    rw [fields_toNat f neg E T hE hT, hwt, ht2]
    have : E * (2 * 2 ^ (f.t - 1)) = 2 * (E * 2 ^ (f.t - 1)) := by ac_rfl
    rw [this]
    cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  unfold EvenSig ulpExp at he
  unfold finite
  by_cases hlt : u < 2 ^ f.t
  · rw [if_pos hlt]
    apply parity 0 u (Nat.two_pow_pos _) hlt
    by_cases h0 : u = 0
    · simp [h0]
    · have : u.log2 < f.t := (Nat.log2_lt h0).2 hlt
      have : u.log2 + 1 - f.p = 0 := by simp only [Format.t] at this; omega
      rwa [this, Nat.pow_zero, Nat.div_one] at he
  · rw [if_neg hlt]
    simp only []
    have hu0 : u ≠ 0 := by have := Nat.two_pow_pos f.t; omega
    have hl : f.t ≤ u.log2 := (Nat.le_log2 hu0).2 (by omega)
    have hj : u.log2 + 1 - f.p = u.log2 - f.t := by simp only [Format.t]; omega
    rw [hj] at he
    obtain ⟨hlo, hT, hj2⟩ := normal_bounds f u hmax (by omega)
    generalize u.log2 - f.t = j at *
    exact parity (j + 1) _ (by omega) hT (by omega)

theorem natAbs_units_same (f : Format) (σ : Bool) (u Nq Dq : Nat) :
    (sgn σ u * Dq - sgn σ Nq * 2 ^ f.scale).natAbs = udist (Nq * 2 ^ f.scale) Dq u := by
  have : (2 : Int) ^ f.scale = ((2 ^ f.scale : Nat) : Int) := by simp
  rw [this, sgn_mul, sgn_mul, natAbs_sgn_same]; rfl

theorem natAbs_units_opp (f : Format) (σ : Bool) (u Nq Dq : Nat) :
    (sgn (!σ) u * Dq - sgn σ Nq * 2 ^ f.scale).natAbs = u * Dq + Nq * 2 ^ f.scale := by
  have : (2 : Int) ^ f.scale = ((2 ^ f.scale : Nat) : Int) := by simp
  rw [this, sgn_mul, sgn_mul, natAbs_sgn_opp]

/-- The shared core of both cases: a result `finite f σ u` whose units `u` are nearest to
`Nq·2^scale / Dq` (ties to even) satisfies both clauses of `DivideIsNearestTiesToEven`. -/
theorem nearest_core (f : Format) (σ : Bool) (Nq Dq u : Nat) (hD : 0 < Dq) (hu : RepU f u)
    (hmax : u ≤ f.maxUnits)
    (hnear : ∀ w, RepU f w → udist (Nq * 2 ^ f.scale) Dq u ≤ udist (Nq * 2 ^ f.scale) Dq w)
    (htie : ∀ w, RepU f w → w ≠ u →
      udist (Nq * 2 ^ f.scale) Dq w ≤ udist (Nq * 2 ^ f.scale) Dq u → EvenSig f u)
    (r : Int × Nat) (hr : (decode f (finite f σ u)).value? = some r) :
    (∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
        NoFarther r v (sgn σ Nq, Dq)) ∧
    (∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
        v.1 * r.2 ≠ r.1 * v.2 → NoFarther v r (sgn σ Nq, Dq) →
        (finite f σ u).toNat % 2 = 0) := by
  obtain ⟨r', hr', hrU⟩ := decode_encode f σ u hu hmax
  rw [hr'] at hr; cases hr
  have h0 := hnear 0 (zero_rep f)
  have hd0 : udist (Nq * 2 ^ f.scale) Dq 0 = Nq * 2 ^ f.scale := by simp [udist]
  constructor
  · intro z v hv
    obtain ⟨σv, u', hu', hvU⟩ := value_decode f z v hv
    apply (noFarther_iff_units f r v σ σv σ u u' Nq Dq hrU hvU).mpr
    rw [natAbs_units_same]
    cases hσ : σv == σ
    · have : σv = !σ := by cases σv <;> cases σ <;> simp_all
      subst this
      rw [natAbs_units_opp]; omega
    · have : σv = σ := by simpa using hσ
      subst this
      rw [natAbs_units_same]; exact hnear u' hu'
  · intro z v hv hne hle
    obtain ⟨σv, u', hu', hvU⟩ := value_decode f z v hv
    have hle := (noFarther_iff_units f v r σv σ σ u' u Nq Dq hvU hrU).mp hle
    rw [natAbs_units_same] at hle
    apply finite_lsb f σ u hmax
    cases hσ : σv == σ
    · have : σv = !σ := by cases σv <;> cases σ <;> simp_all
      subst this
      rw [natAbs_units_opp] at hle
      have hu'0 : u' = 0 := by
        rcases Nat.eq_zero_or_pos u' with h | h
        · exact h
        · have := Nat.mul_pos h hD; omega
      subst hu'0
      by_cases hu0 : u = 0
      · subst hu0
        exact absurd (eqv_of_units f v r _ σ 0 0 hvU hrU (by cases σ <;> rfl)) hne
      · exact htie 0 (zero_rep f) (Ne.symm hu0) (by omega)
    · have : σv = σ := by simpa using hσ
      subst this
      rw [natAbs_units_same] at hle
      by_cases heq : u' = u
      · subst heq; exact absurd (eqv_of_units f v r σv σv u' u' hvU hrU rfl) hne
      · exact htie u' hu' heq hle

/-- The named signed zero is the encoder `finite` at 0 units. -/
theorem zero_eq_finite (f : Format) (neg : Bool) : zero f neg = finite f neg 0 := by
  unfold zero finite
  rw [if_pos (Nat.two_pow_pos _)]

theorem divide_zero_finite (f : Format) (m : RoundingMode) (a b : BitVec f.k) (sa sb : Bool)
    (qb : Int) (cb : Nat) (ha : decode f a = .zero sa) (hb : decode f b = .finite sb qb cb) :
    divide f m a b = finite f (sa ^^ sb) 0 := by
  simp only [divide, ha, hb, zero_eq_finite]

theorem divide_finite_finite (f : Format) (m : RoundingMode) (a b : BitVec f.k) (sa sb : Bool)
    (qa qb : Int) (ca cb : Nat) (ha : decode f a = .finite sa qa ca)
    (hb : decode f b = .finite sb qb cb) :
    divide f m a b = round f m (sa ^^ sb) (ca * 2 ^ qa.toNat * 2 ^ (-qb).toNat)
      (2 ^ (-qa).toNat * (cb * 2 ^ qb.toNat)) := by
  simp only [divide, ha, hb]

/-- **Main theorem**: `divide` under roundTiesToEven returns the nearest finite number, ties to
even, for every format (the statement is `DivideIsNearestTiesToEven` in `IEEE754.lean`). -/
theorem divide_isNearestTiesToEven (f : Format) : DivideIsNearestTiesToEven f := by
  intro a b x y r hx hy hy0 hr
  -- the divisor is finite and nonzero
  obtain ⟨sb, qb, cb, hb⟩ : ∃ sb qb cb, decode f b = .finite sb qb cb := by
    cases hb : decode f b with
    | finite sb qb cb => exact ⟨sb, qb, cb, rfl⟩
    | zero sb => rw [hb] at hy; cases hy; exact absurd rfl hy0
    | nan _ => rw [hb] at hy; cases hy
    | inf _ => rw [hb] at hy; cases hy
  rw [hb, value_finite_eq] at hy
  cases hy
  have hny : cb * 2 ^ qb.toNat ≠ 0 := by
    intro h; apply hy0; simp only [h, sgn]; cases sb <;> rfl
  have hdq : 0 < 2 ^ (-qb).toNat := Nat.two_pow_pos _
  cases ha : decode f a with
  | nan _ => rw [ha] at hx; cases hx
  | inf _ => rw [ha] at hx; cases hx
  | zero sa =>
    rw [ha] at hx; cases hx
    have hx0 : ((0 : Int), (1 : Nat)) = (sgn sa 0, 1) := by cases sa <;> rfl
    rw [hx0, fracDiv_sgn sa sb 0 1 _ _ hny]
    rw [divide_zero_finite f _ a b sa sb qb cb ha hb] at hr ⊢
    refine nearest_core f _ _ _ 0 (by omega) (zero_rep f) (Nat.zero_le _) ?_ ?_ r hr
    · intro w _; simp [udist]
    · intro w _ hw0 hle
      unfold udist at hle
      have := Nat.mul_pos (Nat.pos_of_ne_zero hw0)
        (show 0 < 1 * (cb * 2 ^ qb.toNat) by omega)
      omega
  | finite sa qa ca =>
    rw [ha, value_finite_eq] at hx; cases hx
    rw [fracDiv_sgn sa sb _ _ _ _ hny]
    rw [divide_finite_finite f _ a b sa sb qa qb ca cb ha hb] at hr ⊢
    have hD : 0 < 2 ^ (-qa).toNat * (cb * 2 ^ qb.toNat) :=
      Nat.mul_pos (Nat.two_pow_pos _) (Nat.pos_of_ne_zero hny)
    unfold round at hr ⊢
    simp only at hr ⊢
    split
    · next hmax =>
      rw [if_pos hmax] at hr
      exact nearest_core f _ _ _ _ hD (rne_rep f _ _ _) hmax
        (rne_nearest f _ _ _ hD) (fun w hw hne hle => rne_tie_even f _ _ _ hD w hw hne hle) r hr
    · next hmax =>
      rw [if_neg hmax] at hr
      simp [overflowToInfinity, decode_infinity, Datum.value?] at hr

theorem natAbs_sgn (s : Bool) (n : Nat) : (sgn s n).natAbs = n := by
  cases s <;> simp [sgn]

/-- The units form of the threshold is the fraction form times `2^(emax−1)`. -/
theorem threshold_units_iff (f : Format) (Nq Dq : Nat) :
    Dq * (2 * f.maxUnits + 2 ^ (2 * f.emax - 1)) ≤ 2 * (Nq * 2 ^ f.scale) ↔
      Dq * 2 ^ f.emax * (2 ^ (f.p + 1) - 1) ≤ Nq * 2 ^ f.p := by
  have hp := f.hp
  have he := emax_pos f
  have hK := Nat.two_pow_pos (f.emax - 1)
  have hJ : 2 ^ (2 * f.emax - 1) = 2 ^ f.emax * 2 ^ (f.emax - 1) := by
    rw [← Nat.pow_add]; congr 1; omega
  have eL : Dq * (2 * f.maxUnits + 2 ^ (2 * f.emax - 1)) =
      Dq * 2 ^ f.emax * (2 ^ (f.p + 1) - 1) * 2 ^ (f.emax - 1) := by
    rw [maxUnits_eq, hJ, Nat.pow_succ,
      show Dq * 2 ^ f.emax * (2 ^ f.p * 2 - 1) * 2 ^ (f.emax - 1) =
        Dq * ((2 ^ f.p * 2 - 1) * (2 ^ f.emax * 2 ^ (f.emax - 1))) by ac_rfl]
    congr 1
    generalize 2 ^ f.emax * 2 ^ (f.emax - 1) = Y
    have hX := Nat.two_pow_pos f.p
    generalize 2 ^ f.p = X at *
    rw [Nat.sub_mul, Nat.sub_mul, Nat.one_mul, Nat.mul_right_comm X 2 Y]
    have := Nat.le_mul_of_pos_left Y hX
    omega
  have eR : 2 * (Nq * 2 ^ f.scale) = Nq * 2 ^ f.p * 2 ^ (f.emax - 1) := by
    rw [Nat.mul_assoc, ← Nat.pow_add, Nat.mul_left_comm, ← Nat.pow_succ']
    congr 2; unfold Format.scale; simp only [Format.t]; omega
  rw [eL, eR]
  exact ⟨fun h => Nat.le_of_mul_le_mul_right h hK, fun h => Nat.mul_le_mul_right _ h⟩

/-- **Second theorem**: overflow happens exactly at the §4.3.1 threshold (the statement is
`DivideOverflowsAtThreshold` in `IEEE754.lean`). -/
theorem divide_overflowsAtThreshold (f : Format) : DivideOverflowsAtThreshold f := by
  intro a b x y hx hy hy0
  obtain ⟨sb, qb, cb, hb⟩ : ∃ sb qb cb, decode f b = .finite sb qb cb := by
    cases hb : decode f b with
    | finite sb qb cb => exact ⟨sb, qb, cb, rfl⟩
    | zero sb => rw [hb] at hy; cases hy; exact absurd rfl hy0
    | nan _ => rw [hb] at hy; cases hy
    | inf _ => rw [hb] at hy; cases hy
  rw [hb, value_finite_eq] at hy
  cases hy
  have hny : cb * 2 ^ qb.toNat ≠ 0 := by
    intro h; apply hy0; simp only [h, sgn]; cases sb <;> rfl
  cases ha : decode f a with
  | nan _ => rw [ha] at hx; cases hx
  | inf _ => rw [ha] at hx; cases hx
  | zero sa =>
    rw [ha] at hx; cases hx
    have hx0 : ((0 : Int), (1 : Nat)) = (sgn sa 0, 1) := by cases sa <;> rfl
    rw [hx0, fracDiv_sgn sa sb 0 1 _ _ hny, divide_zero_finite f _ a b sa sb qb cb ha hb]
    obtain ⟨r', hr', -⟩ := decode_encode f (sa ^^ sb) 0 (zero_rep f) (Nat.zero_le _)
    simp only [natAbs_sgn, Nat.zero_mul]
    constructor
    · rintro ⟨s, hs⟩; rw [hs] at hr'; cases hr'
    · intro h
      have h1 : 0 < 1 * (cb * 2 ^ qb.toNat) := by omega
      have h2 : 0 < 2 ^ (f.p + 1) - 1 := by
        have := Nat.one_lt_two_pow (n := f.p + 1) (by omega); omega
      have := Nat.mul_pos (Nat.mul_pos h1 (Nat.two_pow_pos f.emax)) h2
      omega
  | finite sa qa ca =>
    rw [ha, value_finite_eq] at hx; cases hx
    rw [fracDiv_sgn sa sb _ _ _ _ hny, divide_finite_finite f _ a b sa sb qa qb ca cb ha hb]
    have hD : 0 < 2 ^ (-qa).toNat * (cb * 2 ^ qb.toNat) :=
      Nat.mul_pos (Nat.two_pow_pos _) (Nat.pos_of_ne_zero hny)
    simp only [natAbs_sgn]
    rw [← threshold_units_iff, ← rne_overflow_iff f (sa ^^ sb) _ _ hD]
    unfold round
    simp only
    split
    · next hmax =>
      obtain ⟨r', hr', -⟩ := decode_encode f (sa ^^ sb) _ (rne_rep f _ _ _) hmax
      constructor
      · rintro ⟨s, hs⟩; rw [hs] at hr'; cases hr'
      · intro h; omega
    · next hmax =>
      simp only [overflowToInfinity, ↓reduceIte, decode_infinity]
      exact ⟨fun _ => by omega, fun _ => ⟨_, rfl⟩⟩

/-- Every non-NaN datum `decode` returns carries the pattern's most significant bit as sign. -/
theorem decode_sign (f : Format) (a : BitVec f.k) :
    (∃ sg, decode f a = .nan sg) ∨ decode f a = .inf a.msb ∨ decode f a = .zero a.msb ∨
      ∃ q c, decode f a = .finite a.msb q c := by
  rw [msb_eq_S]
  unfold decode
  simp only
  split
  · split
    · exact .inr (.inl rfl)
    · exact .inl ⟨_, rfl⟩
  · split
    · split
      · exact .inr (.inr (.inl rfl))
      · exact .inr (.inr (.inr ⟨_, _, rfl⟩))
    · exact .inr (.inr (.inr ⟨_, _, rfl⟩))

theorem fields_msb (f : Format) (neg : Bool) (E T : Nat) (hE : E < 2 ^ f.w)
    (hT : T < 2 ^ f.t) : (fields f neg E T).msb = neg := by
  have hlow : E * 2 ^ f.t + T < 2 ^ (f.w + f.t) := by
    rw [Nat.pow_add]
    have : (E + 1) * 2 ^ f.t ≤ 2 ^ f.w * 2 ^ f.t := Nat.mul_le_mul_right _ hE
    rw [Nat.succ_mul] at this; omega
  rw [msb_eq_S, fields_toNat f neg E T hE hT, Nat.add_comm,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlow, Nat.zero_add]
  cases neg <;> rfl

/-- Within the finite range, the encoder `finite` writes a biased exponent below `2^w − 1`. -/
theorem finite_fields (f : Format) (neg : Bool) (u : Nat) (hmax : u ≤ f.maxUnits) :
    ∃ E T, E < 2 ^ f.w - 1 ∧ T < 2 ^ f.t ∧ finite f neg u = fields f neg E T := by
  have hw2 := two_emax f
  unfold finite
  by_cases hlt : u < 2 ^ f.t
  · rw [if_pos hlt]; exact ⟨0, u, by omega, hlt, rfl⟩
  · rw [if_neg hlt]
    obtain ⟨-, hT, hj2⟩ := normal_bounds f u hmax (by omega)
    exact ⟨_, _, hj2, hT, rfl⟩

theorem finite_msb (f : Format) (neg : Bool) (u : Nat) (hmax : u ≤ f.maxUnits) :
    (finite f neg u).msb = neg := by
  obtain ⟨E, T, hE, hT, h⟩ := finite_fields f neg u hmax
  rw [h, fields_msb f neg E T (by omega) hT]

/-- Within the finite range, the encoder `finite` produces a zero or finite number. -/
theorem finite_hasValue (f : Format) (neg : Bool) (u : Nat) (hmax : u ≤ f.maxUnits) :
    ∃ r, (decode f (finite f neg u)).value? = some r := by
  obtain ⟨E, T, hE, hT, h⟩ := finite_fields f neg u hmax
  rw [h, decode_fields f neg E T (by omega) hT, if_neg (by omega)]
  split
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem infinity_msb (f : Format) (neg : Bool) : (infinity f neg).msb = neg := by
  unfold infinity
  exact fields_msb f neg _ _ (by have := Nat.two_pow_pos f.w; omega) (Nat.two_pow_pos _)

theorem zero_msb (f : Format) (neg : Bool) : (zero f neg).msb = neg := by
  unfold zero
  exact fields_msb f neg 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _)

theorem decode_canonicalNaN (f : Format) : decode f (canonicalNaN f) = .nan false := by
  have hp := f.hp
  have ht : 2 ^ (f.t - 1) < 2 ^ f.t :=
    Nat.pow_lt_pow_right (by omega) (by simp only [Format.t]; omega)
  unfold canonicalNaN
  rw [decode_fields f false _ _ (by have := Nat.two_pow_pos f.w; omega) ht, if_pos rfl,
    if_neg (Nat.ne_of_gt (Nat.two_pow_pos _))]
  simp

/-- `round` always delivers the sign it is given (§6.3), overflow results included. -/
theorem round_msb (f : Format) (mode : RoundingMode) (neg : Bool) (n d : Nat) :
    (round f mode neg n d).msb = neg := by
  unfold round
  simp only
  split
  · next hmax => exact finite_msb f neg _ hmax
  · split
    · exact infinity_msb f neg
    · exact finite_msb f neg _ (Nat.le_refl _)

/-- `round` never delivers a NaN: an infinity, or a zero or finite number. -/
theorem round_notNaN (f : Format) (mode : RoundingMode) (neg : Bool) (n d : Nat) :
    (∃ s, decode f (round f mode neg n d) = .inf s) ∨
      ∃ r, (decode f (round f mode neg n d)).value? = some r := by
  unfold round
  simp only
  split
  · next hmax => exact .inr (finite_hasValue f neg _ hmax)
  · split
    · exact .inl ⟨_, decode_infinity f neg⟩
    · exact .inr (finite_hasValue f neg _ (Nat.le_refl _))

/-- **Third theorem**: a quotient of two numbers with a nonzero divisor is never a NaN, under
every rounding-direction attribute (the statement is `DivideOfNumbersIsNotNaN` in
`IEEE754.lean`). -/
theorem divide_ofNumbersIsNotNaN (f : Format) : DivideOfNumbersIsNotNaN f := by
  intro mode a b x y hx hy hy0
  obtain ⟨sb, qb, cb, hb⟩ : ∃ sb qb cb, decode f b = .finite sb qb cb := by
    cases hb : decode f b with
    | finite sb qb cb => exact ⟨sb, qb, cb, rfl⟩
    | zero sb => rw [hb] at hy; cases hy; exact absurd rfl hy0
    | nan _ => rw [hb] at hy; cases hy
    | inf _ => rw [hb] at hy; cases hy
  cases ha : decode f a with
  | nan _ => rw [ha] at hx; cases hx
  | inf _ => rw [ha] at hx; cases hx
  | zero sa =>
    rw [divide_zero_finite f mode a b sa sb qb cb ha hb]
    exact .inr (finite_hasValue f _ 0 (Nat.zero_le _))
  | finite sa qa ca =>
    rw [divide_finite_finite f mode a b sa sb qa qb ca cb ha hb]
    exact round_notNaN f mode _ _ _

/-- **Fourth theorem**: every non-NaN quotient has the XOR of the operands' sign bits, for all
bit patterns and every rounding-direction attribute (the statement is `DivideSignIsXor` in
`IEEE754.lean`). -/
theorem divide_signIsXor (f : Format) : DivideSignIsXor f := by
  intro mode a b hnan
  have hN := decode_canonicalNaN f
  rcases decode_sign f a with ⟨sa, ha⟩ | ha | ha | ⟨qa, ca, ha⟩ <;>
  rcases decode_sign f b with ⟨sb, hb⟩ | hb | hb | ⟨qb, cb, hb⟩ <;>
  simp only [divide, ha, hb] at hnan ⊢ <;>
  -- `rw` matches the encoders syntactically, so a wrong alternative fails at once
  first
    | rw [infinity_msb]
    | rw [zero_msb]
    | rw [round_msb]
    | exact absurd hN (hnan false)

/-- An infinity pattern is `infinity f s`. -/
theorem decode_inf_eq (f : Format) (R : BitVec f.k) (s : Bool) (h : decode f R = .inf s) :
    R = infinity f s := by
  have hR := eq_fields f R
  have hEl := Nat.mod_lt (R.toNat / 2 ^ f.t) (Nat.two_pow_pos f.w)
  have hTl := Nat.mod_lt R.toNat (Nat.two_pow_pos f.t)
  generalize R.toNat / 2 ^ f.t % 2 ^ f.w = E at hR hEl
  generalize R.toNat % 2 ^ f.t = T at hR hTl
  generalize R.msb = σ at hR
  rw [hR, decode_fields f σ E T hEl hTl] at h
  rw [hR]
  split at h
  · next hE =>
    split at h
    · next hT => cases h; subst hE; subst hT; rfl
    · cases h
  · split at h
    · split at h <;> cases h
    · cases h

/-- A pattern with a value is the encoding (`finite`) of its magnitude `u` in units, with its
own sign bit; `u` is representable and at most `maxUnits`. -/
theorem decode_value_pattern (f : Format) (R : BitVec f.k) (r : Int × Nat)
    (h : (decode f R).value? = some r) :
    ∃ u, u ≤ f.maxUnits ∧ RepU f u ∧ IsUnits f r R.msb u ∧ R = finite f R.msb u := by
  have hp := f.hp
  have hw2 := two_emax f
  have he := emax_pos f
  have hR := eq_fields f R
  have hEl := Nat.mod_lt (R.toNat / 2 ^ f.t) (Nat.two_pow_pos f.w)
  have hTl := Nat.mod_lt R.toNat (Nat.two_pow_pos f.t)
  generalize R.toNat / 2 ^ f.t % 2 ^ f.w = E at hR hEl
  generalize R.toNat % 2 ^ f.t = T at hR hTl
  generalize R.msb = σ at hR ⊢
  rw [hR, decode_fields f σ E T hEl hTl] at h
  rw [hR]
  have ht : 2 ^ f.t + 2 ^ f.t = 2 ^ f.p := by
    rw [← Nat.two_mul, ← Nat.pow_succ']; congr 1; simp only [Format.t]; omega
  have hmaxp : 2 ^ f.p - 1 ≤ f.maxUnits := by
    unfold Format.maxUnits
    exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  split at h
  · split at h <;> simp [Datum.value?] at h
  · split at h
    · next hE0 =>
      subst hE0
      split at h
      · next hT0 =>
        subst hT0
        simp only [Datum.value?, Option.some.injEq] at h
        subst h
        exact ⟨0, Nat.zero_le _, zero_rep f, ⟨by decide, by simp⟩, zero_eq_finite f σ⟩
      · obtain ⟨v, hv, hU⟩ := value_finite f σ (f.emin - f.t) T (Int.le_refl _)
        rw [hv] at h; cases h
        have e : (f.emin - f.t - f.qmin).toNat = 0 := by unfold Format.qmin; omega
        rw [e, Nat.pow_zero, Nat.mul_one] at hU
        refine ⟨T, by omega, ⟨T, 0, by omega, by simp⟩, hU, ?_⟩
        unfold finite; rw [if_pos hTl]
    · next hEm hE0 =>
      have hq : f.qmin ≤ (E : Int) - f.emax - f.t := by
        unfold Format.qmin Format.emin; omega
      obtain ⟨v, hv, hU⟩ := value_finite f σ ((E : Int) - f.emax - f.t) (2 ^ f.t + T) hq
      rw [hv] at h; cases h
      have e : ((E : Int) - f.emax - f.t - f.qmin).toNat = E - 1 := by
        unfold Format.qmin Format.emin; omega
      rw [e] at hU
      refine ⟨(2 ^ f.t + T) * 2 ^ (E - 1), ?_, ⟨2 ^ f.t + T, E - 1, by omega, rfl⟩, hU, ?_⟩
      · unfold Format.maxUnits
        exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
      · have hc0 : 2 ^ f.t + T ≠ 0 := by omega
        have hlog : (2 ^ f.t + T).log2 = f.t := by
          rw [Nat.log2_eq_iff hc0, Nat.pow_succ]; omega
        have hge : ¬ (2 ^ f.t + T) * 2 ^ (E - 1) < 2 ^ f.t := by
          have := Nat.le_mul_of_pos_right (2 ^ f.t + T) (Nat.two_pow_pos (E - 1)); omega
        unfold finite
        rw [if_neg hge]
        simp only []
        rw [log2_mul_two_pow _ hc0, hlog, show f.t + (E - 1) - f.t = E - 1 by omega,
          Nat.mul_div_cancel _ (Nat.two_pow_pos _), show E - 1 + 1 = E by omega,
          show 2 ^ f.t + T - 2 ^ f.t = T by omega]

/-- The last bit of an encoded magnitude is the last bit of its significand at its own
spacing (the subnormal `T`, or the integral significand `c`). -/
theorem finite_mod_two (f : Format) (neg : Bool) (u : Nat) (hmax : u ≤ f.maxUnits) :
    (finite f neg u).toNat % 2 = u / 2 ^ ulpExp f u % 2 := by
  have hp := f.hp
  have hw2 := two_emax f
  have ht2 : 2 ^ f.t = 2 * 2 ^ (f.t - 1) := by
    rw [← Nat.pow_succ']; congr 1; simp only [Format.t]; omega
  have hwt : 2 ^ (f.w + f.t) = 2 * 2 ^ (f.w + f.t - 1) := by
    rw [← Nat.pow_succ']; congr 1; simp only [Format.t]; omega
  have parity : ∀ E T, E < 2 ^ f.w → T < 2 ^ f.t → (fields f neg E T).toNat % 2 = T % 2 := by
    intro E T hE hT
    rw [fields_toNat f neg E T hE hT, hwt, ht2]
    have : E * (2 * 2 ^ (f.t - 1)) = 2 * (E * 2 ^ (f.t - 1)) := by ac_rfl
    rw [this]
    cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  unfold ulpExp finite
  by_cases hlt : u < 2 ^ f.t
  · rw [if_pos hlt, parity 0 u (Nat.two_pow_pos _) hlt]
    by_cases h0 : u = 0
    · simp [h0]
    · have : u.log2 < f.t := (Nat.log2_lt h0).2 hlt
      have : u.log2 + 1 - f.p = 0 := by simp only [Format.t] at this; omega
      rw [this, Nat.pow_zero, Nat.div_one]
  · rw [if_neg hlt]
    simp only []
    have hu0 : u ≠ 0 := by have := Nat.two_pow_pos f.t; omega
    have hl : f.t ≤ u.log2 := (Nat.le_log2 hu0).2 (by omega)
    have hj : u.log2 + 1 - f.p = u.log2 - f.t := by simp only [Format.t]; omega
    rw [hj]
    obtain ⟨hlo, hT, hj2⟩ := normal_bounds f u hmax (by omega)
    generalize u.log2 - f.t = j at *
    rw [parity (j + 1) _ (by omega) hT]
    omega

/-- A value read off a pattern is `±n / d` with the pattern's sign bit, `d > 0`. -/
theorem value_sgn (f : Format) (a : BitVec f.k) (x : Int × Nat)
    (h : (decode f a).value? = some x) : ∃ n d, 0 < d ∧ x = (sgn a.msb n, d) := by
  rcases decode_sign f a with ⟨_, h'⟩ | h' | h' | ⟨q, c, h'⟩ <;> rw [h'] at h
  · simp [Datum.value?] at h
  · simp [Datum.value?] at h
  · simp only [Datum.value?, Option.some.injEq] at h
    subst h
    refine ⟨0, 1, by decide, ?_⟩
    generalize a.msb = s
    cases s <;> rfl
  · rw [value_finite_eq] at h
    cases h
    exact ⟨_, _, Nat.two_pow_pos _, rfl⟩

/-- The exact quotient of two values read off patterns, with the XOR sign. -/
theorem quotient_sgn (f : Format) (a b : BitVec f.k) (x y : Int × Nat)
    (hx : (decode f a).value? = some x) (hy : (decode f b).value? = some y) (hy0 : y.1 ≠ 0) :
    ∃ N D, 0 < D ∧ fracDiv x y = (sgn (a.msb ^^ b.msb) N, D) := by
  obtain ⟨nx, dx, hdx, rfl⟩ := value_sgn f a x hx
  obtain ⟨ny, dy, hdy, rfl⟩ := value_sgn f b y hy
  have hny : ny ≠ 0 := by
    rintro rfl
    apply hy0
    generalize b.msb = s
    cases s <;> rfl
  exact ⟨_, _, Nat.mul_pos hdx (Nat.pos_of_ne_zero hny), fracDiv_sgn _ _ _ _ _ _ hny⟩

/-- Distinct magnitudes of one sign are distinct fractions. -/
theorem units_ne (f : Format) (r v : Int × Nat) (σ : Bool) (u1 u2 : Nat)
    (hr : IsUnits f r σ u1) (hv : IsUnits f v σ u2) (hne : u1 ≠ u2) :
    v.1 * r.2 ≠ r.1 * v.2 := by
  intro h
  apply hne
  rw [isUnits_sgn] at hr hv
  have hpos : (0 : Int) < (r.2 : Int) * v.2 := by
    have := hr.1; have := hv.1
    exact Int.mul_pos (by omega) (by omega)
  have key : sgn σ u1 * ((r.2 : Int) * v.2) = sgn σ u2 * ((r.2 : Int) * v.2) := by
    calc sgn σ u1 * ((r.2 : Int) * v.2) = r.1 * 2 ^ f.scale * v.2 := by rw [hr.2]; ac_rfl
      _ = r.1 * v.2 * 2 ^ f.scale := by ac_rfl
      _ = v.1 * r.2 * 2 ^ f.scale := by rw [h]
      _ = v.1 * 2 ^ f.scale * r.2 := by ac_rfl
      _ = sgn σ u2 * ((r.2 : Int) * v.2) := by rw [hv.2]; ac_rfl
  have := Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hpos) key
  cases σ <;> simp only [sgn, Bool.false_eq_true, ↓reduceIte] at this <;> omega

theorem noFarther_iff_udist (f : Format) (r v : Int × Nat) (σ : Bool) (u u' N D : Nat)
    (hr : IsUnits f r σ u) (hv : IsUnits f v σ u') :
    NoFarther r v (sgn σ N, D) ↔
      udist (N * 2 ^ f.scale) D u ≤ udist (N * 2 ^ f.scale) D u' := by
  rw [noFarther_iff_units f r v σ σ σ u u' N D hr hv, natAbs_units_same, natAbs_units_same]

/-- A magnitude `u` of sign `σ` (the value `r`) that is nearest to `±N / D` among the patterns
of the format, and has an even significand whenever another pattern is equally near, is the
roundTiesToEven magnitude, provided that one is finite. -/
theorem units_eq_rne (f : Format) (σ : Bool) (N D u : Nat) (hD : 0 < D) (r : Int × Nat)
    (hu : RepU f u) (hR : IsUnits f r σ u)
    (hstar : roundUnits f .nearestTiesToEven σ (N * 2 ^ f.scale) D ≤ f.maxUnits)
    (hnear : ∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
        NoFarther r v (sgn σ N, D))
    (htie : ∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
        v.1 * r.2 ≠ r.1 * v.2 → NoFarther v r (sgn σ N, D) → EvenSig f u) :
    u = roundUnits f .nearestTiesToEven σ (N * 2 ^ f.scale) D := by
  obtain ⟨p, hp, hpU⟩ := decode_encode f σ _ (rne_rep f _ _ _) hstar
  have hle := (noFarther_iff_udist f r p σ u _ N D hR hpU).mp (hnear _ p hp)
  apply Classical.byContradiction
  intro hne
  have hsle := rne_nearest f σ (N * 2 ^ f.scale) D hD u hu
  have hev : EvenSig f u := htie _ p hp (units_ne f r p σ u _ hR hpU hne)
    ((noFarther_iff_udist f p r σ _ u N D hpU hR).mpr hsle)
  exact rne_two_even f σ _ D hD u hu hne hle hev

/-- The pattern singled out by the four properties, for sign `σ` and exact quotient `q`. -/
def canonQuot (f : Format) (σ : Bool) (q : Int × Nat) : BitVec f.k :=
  if q.2 * 2 ^ f.emax * (2 ^ (f.p + 1) - 1) ≤ q.1.natAbs * 2 ^ f.p then infinity f σ
  else finite f σ (roundUnits f .nearestTiesToEven σ (q.1.natAbs * 2 ^ f.scale) q.2)

/-- Any pattern with the four properties is `canonQuot`. -/
theorem eq_canonQuot (f : Format) (a b R : BitVec f.k) (x y : Int × Nat)
    (hx : (decode f a).value? = some x) (hy : (decode f b).value? = some y) (hy0 : y.1 ≠ 0)
    (h1 : (∃ s, decode f R = .inf s) ∨ ∃ r, (decode f R).value? = some r)
    (h2 : R.msb = (a.msb ^^ b.msb))
    (h3 : (∃ s, decode f R = .inf s) ↔
      (fracDiv x y).2 * 2 ^ f.emax * (2 ^ (f.p + 1) - 1) ≤ (fracDiv x y).1.natAbs * 2 ^ f.p)
    (h4 : ∀ r, (decode f R).value? = some r →
      (∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
          NoFarther r v (fracDiv x y)) ∧
      (∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
          v.1 * r.2 ≠ r.1 * v.2 → NoFarther v r (fracDiv x y) → R.toNat % 2 = 0)) :
    R = canonQuot f (a.msb ^^ b.msb) (fracDiv x y) := by
  obtain ⟨N, D, hD, hxy⟩ := quotient_sgn f a b x y hx hy hy0
  rw [hxy] at h3 h4 ⊢
  generalize (a.msb ^^ b.msb) = σ at h2 h4 ⊢
  unfold canonQuot
  simp only [natAbs_sgn] at h3 ⊢
  split
  · next hT =>
    obtain ⟨s, hs⟩ := h3.mpr hT
    have hRs := decode_inf_eq f R s hs
    rw [hRs, infinity_msb] at h2
    rw [hRs, h2]
  · next hT =>
    obtain ⟨r, hr⟩ := h1.resolve_left (fun h => hT (h3.mp h))
    obtain ⟨u, hmax, hu, hU, hReq⟩ := decode_value_pattern f R r hr
    rw [h2] at hU hReq
    have hstar : roundUnits f .nearestTiesToEven σ (N * 2 ^ f.scale) D ≤ f.maxUnits :=
      Nat.le_of_not_lt fun h =>
        hT ((threshold_units_iff f N D).mp ((rne_overflow_iff f σ _ D hD).mp h))
    rw [hReq, units_eq_rne f σ N D u hD r hu hU hstar (h4 r hr).1 fun z v hv hne hle => by
      have := (h4 r hr).2 z v hv hne hle
      rw [hReq, finite_mod_two f σ u hmax] at this
      exact this]

/-- An infinity or a pattern with a value is not a NaN. -/
theorem not_nan_of (f : Format) (R : BitVec f.k)
    (h : (∃ s, decode f R = .inf s) ∨ ∃ r, (decode f R).value? = some r) :
    ∀ s, decode f R ≠ .nan s := by
  intro s hs
  rcases h with ⟨s', hs'⟩ | ⟨r, hr⟩
  · rw [hs] at hs'; cases hs'
  · rw [hs] at hr; simp [Datum.value?] at hr

/-- **Fifth theorem**: the four properties determine the roundTiesToEven quotient (the
statement is `DivideIsUniquelyCharacterized` in `IEEE754.lean`). -/
theorem divide_isUniquelyCharacterized (f : Format) : DivideIsUniquelyCharacterized f := by
  intro a b R x y hx hy hy0 h1 h2 h3 h4
  have g1 := divide_ofNumbersIsNotNaN f .nearestTiesToEven a b x y hx hy hy0
  have g2 := divide_signIsXor f .nearestTiesToEven a b (not_nan_of f _ g1)
  rw [eq_canonQuot f a b R x y hx hy hy0 h1 (h2 (not_nan_of f R h1)) h3 h4,
    eq_canonQuot f a b _ x y hx hy hy0 g1 g2 (divide_overflowsAtThreshold f a b x y hx hy hy0)
      (fun r hr => divide_isNearestTiesToEven f a b x y r hx hy hy0 hr)]

/-- The challenge instances. -/
example : DivideIsNearestTiesToEven binary16 := divide_isNearestTiesToEven _

example : DivideOverflowsAtThreshold binary16 := divide_overflowsAtThreshold _

example : DivideOfNumbersIsNotNaN binary16 := divide_ofNumbersIsNotNaN _

example : DivideSignIsXor binary16 := divide_signIsXor _

example : DivideIsUniquelyCharacterized binary16 := divide_isUniquelyCharacterized _

example : DivideIsNearestTiesToEven binary32 := divide_isNearestTiesToEven _

example : DivideOverflowsAtThreshold binary32 := divide_overflowsAtThreshold _

example : DivideOfNumbersIsNotNaN binary32 := divide_ofNumbersIsNotNaN _

example : DivideSignIsXor binary32 := divide_signIsXor _

example : DivideIsUniquelyCharacterized binary32 := divide_isUniquelyCharacterized _

/-! ## Division meets the IEEE-level specification `DivisionResult` -/

theorem decode_zero (f : Format) (neg : Bool) : decode f (zero f neg) = .zero neg := by
  unfold zero
  have := four_le_two_pow_w f
  rw [decode_fields f neg 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _), if_neg (by omega), if_pos rfl, if_pos rfl]

theorem round_ne_nan (f : Format) (mode : RoundingMode) (neg : Bool) (n d : Nat) (s : Bool) :
    decode f (round f mode neg n d) ≠ .nan s := by
  intro h
  rcases round_notNaN f mode neg n d with ⟨t, ht⟩ | ⟨r, hr⟩
  · rw [ht] at h; cases h
  · rw [h] at hr; simp [Datum.value?] at hr

/-- A NaN result of `divide` is the canonical NaN (its non-NaN arms are infinities, zeros and rounded values). -/
theorem divide_eq_canonicalNaN (f : Format) (mode : RoundingMode) (a b : BitVec f.k) (s : Bool)
    (hs : decode f (divide f mode a b) = .nan s) : divide f mode a b = canonicalNaN f := by
  unfold divide at hs ⊢
  cases ha : decode f a <;> cases hb : decode f b <;> simp only [ha, hb] at hs ⊢ <;>
    first
    | rfl
    | (rw [decode_infinity] at hs; cases hs)
    | (rw [decode_zero] at hs; cases hs)
    | exact absurd hs (round_ne_nan _ _ _ _ _ _)

/-- **`divide` is a correct IEEE 754 division** in the sense of `DivisionResult`: a non-NaN result is `divide`'s and
a NaN result is a quiet NaN. -/
theorem divide_isResult (f : Format) (mode : RoundingMode) (a b : BitVec f.k) :
    DivisionResult f mode a b (divide f mode a b) := by
  unfold DivisionResult
  by_cases h : ∃ s, decode f (divide f mode a b) = .nan s
  · obtain ⟨s, hs⟩ := h
    refine .inr ⟨⟨s, hs⟩, ?_⟩
    rw [divide_eq_canonicalNaN f mode a b s hs]
    exact decode_canonicalNaN f
  · exact .inl ⟨fun s hs => h ⟨s, hs⟩, rfl⟩

end LeanModels.SoftFloat.Binary
