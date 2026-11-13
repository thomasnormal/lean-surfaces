import LeanModels.SoftFloat.Binary.Cert

/-!
# Division (§5.4.1): the special-case table and the certificate

* `divide_table`: `divide f mode` is the special-case table over the operands' fields (NaN, `∞/∞`, `0/0` give the
  canonical NaN; `∞/y`, `x/0` the XOR-signed infinity; `x/∞`, `0/y` the XOR-signed zero), with the finite/finite arm
  `finQuotF`, for every format and attribute;
* `certF_bridge`: for a nonzero divisor, the roundTiesToEven quotient is the one pattern the certificate `certF`
  (multiplications and comparisons on the fields) accepts.

`divide_isResult` (`divide` meets `DivisionResult`, the IEEE-level specification: any quiet NaN) is in
`Characterization.lean`, beside the facts about NaN results it uses.

Ported from svGolf's fdivp reference proof (section `CertF`), the maintainers' text.
-/

namespace LeanModels.SoftFloat.Binary

open NatFacts

/-- **The finite/finite case**: the `mode`-rounded quotient of two finite nonzero operands,
`|a| / |b| = (sig a · 2^qa) / (sig b · 2^qb)` as the fraction `(nx · dy) / (dx · ny)` with the
XOR sign (the last arm of `divide`, written over the fields). -/
def finQuotF (f : Format) (mode : RoundingMode) (a b : BitVec f.k) : BitVec f.k :=
  let nx := sigF f a * 2 ^ (qexpF f a).toNat
  let dx := 2 ^ (-qexpF f a).toNat
  let ny := sigF f b * 2 ^ (qexpF f b).toNat
  let dy := 2 ^ (-qexpF f b).toNat
  round f mode (signF f a ^^ signF f b) (nx * dy) (dx * ny)

/-- **`divide f mode` is the special-case table of a divider over the operands' fields**, with
the finite/finite case `finQuotF`, for every format, rounding mode and pair of patterns:

* a NaN operand, `∞ / ∞` or `0 / 0`: the canonical NaN;
* otherwise `∞ / y` or `x / 0`: the infinity with the XOR sign;
* otherwise `x / ∞` or `0 / y`: the zero with the XOR sign;
* otherwise both are finite and nonzero: `finQuotF`.

(The conditions are tested in this order, as in `divide` itself and in the reference
design's `always_comb`.) -/
theorem divide_table (f : Format) (mode : RoundingMode) (a b : BitVec f.k) :
    divide f mode a b =
      if isNaNF f a ∨ isNaNF f b ∨ (isInfF f a ∧ isInfF f b) ∨ (isZeroF f a ∧ isZeroF f b) then
        canonicalNaN f
      else if isInfF f a ∨ isZeroF f b then infinity f (signF f a ^^ signF f b)
      else if isInfF f b ∨ isZeroF f a then zero f (signF f a ^^ signF f b)
      else finQuotF f mode a b := by
  have hm : 2 ^ f.w - 1 ≠ 0 := by have := four_le_two_pow_w f; omega
  unfold divide
  rw [decodeF_eq f a, decodeF_eq f b]
  simp only [isNaNF, isInfF, isZeroF, finQuotF, sigF, qexpF, Format.emin]
  by_cases ha31 : expF f a = 2 ^ f.w - 1 <;> by_cases hb31 : expF f b = 2 ^ f.w - 1 <;>
    by_cases ha0 : expF f a = 0 <;> by_cases hb0 : expF f b = 0 <;>
    by_cases ta : fracF f a = 0 <;> by_cases tb : fracF f b = 0 <;>
    simp_all

/-- **The rounding certificate** of a finite nonzero quotient, in every format: `c` is the
roundTiesToEven quotient `a / b` iff `certF f a b c` (`certF_bridge`). With
`e = qexp a - qexp b + scale`, the exact quotient in units of the least subnormal is
`N / D`, `N = sig a · 2^max(e,0)`, `D = sig b · 2^max(-e,0)`. -/
def certF (f : Format) (a b c : BitVec f.k) : Bool :=
  let e : Int := qexpF f a - qexpF f b + f.scale
  certNF f (sigF f a * 2 ^ e.toNat) (sigF f b * 2 ^ (-e).toNat) (signF f a ^^ signF f b) c

/-- The operands' exponents cancel: `roundUnits` of `n·2^scale / d` is that of `N / D`, with
`N = sa · 2^max(e,0)`, `D = sb · 2^max(-e,0)`, `e = qa − qb + scale` (by `roundUnits_scale`). -/
theorem roundUnits_reduceF (f : Format) (mode : RoundingMode) (s : Bool) (sa sb : Nat)
    (qa qb : Int) :
    roundUnits f mode s
        ((sa * 2 ^ qa.toNat * 2 ^ (-qb).toNat) * 2 ^ f.scale)
        (2 ^ (-qa).toNat * (sb * 2 ^ qb.toNat)) =
      roundUnits f mode s (sa * 2 ^ (qa - qb + f.scale).toNat)
        (sb * 2 ^ (-(qa - qb + f.scale)).toNat) := by
  by_cases he : 0 ≤ qa - qb + f.scale
  · have h0 : (-(qa - qb + f.scale)).toNat = 0 := by omega
    rw [h0]
    have := roundUnits_scale f mode s (sa * 2 ^ (qa - qb + f.scale).toNat)
      (sb * 2 ^ 0) ((-qa).toNat + qb.toNat)
    have hN : (sa * 2 ^ qa.toNat * 2 ^ (-qb).toNat) * 2 ^ f.scale =
        sa * 2 ^ (qa - qb + f.scale).toNat * 2 ^ ((-qa).toNat + qb.toNat) := by
      rw [mul_pow_mul_pow_mul_pow, mul_pow_mul_pow]; congr 2; omega
    have hD : 2 ^ (-qa).toNat * (sb * 2 ^ qb.toNat) = sb * 2 ^ 0 * 2 ^ ((-qa).toNat + qb.toNat) := by
      rw [Nat.pow_zero, Nat.mul_one, Nat.pow_add]; ac_rfl
    rw [hN, hD]
    exact this
  · have h0 : (qa - qb + f.scale).toNat = 0 := by omega
    rw [h0]
    have := roundUnits_scale f mode s (sa * 2 ^ 0)
      (sb * 2 ^ (-(qa - qb + f.scale)).toNat) (qa.toNat + (-qb).toNat + f.scale)
    have hN : (sa * 2 ^ qa.toNat * 2 ^ (-qb).toNat) * 2 ^ f.scale =
        sa * 2 ^ 0 * 2 ^ (qa.toNat + (-qb).toNat + f.scale) := by
      rw [mul_pow_mul_pow_mul_pow, Nat.pow_zero, Nat.mul_one]
    have hD : 2 ^ (-qa).toNat * (sb * 2 ^ qb.toNat) =
        sb * 2 ^ (-(qa - qb + f.scale)).toNat * 2 ^ (qa.toNat + (-qb).toNat + f.scale) := by
      rw [mul_pow_mul_pow]
      have e : (-(qa - qb + f.scale)).toNat + (qa.toNat + (-qb).toNat + f.scale) =
          (-qa).toNat + qb.toNat := by
        omega
      rw [e, Nat.pow_add]; ac_rfl
    rw [hN, hD]
    exact this

/-- `finQuotF` under roundTiesToEven is the rounded quotient of the exact quotient in units. -/
theorem finQuotF_eq (f : Format) (a b : BitVec f.k) :
    finQuotF f .nearestTiesToEven a b =
      unitsResultF f (signF f a ^^ signF f b)
        (sigF f a * 2 ^ (qexpF f a - qexpF f b + f.scale).toNat)
        (sigF f b * 2 ^ (-(qexpF f a - qexpF f b + f.scale)).toNat) := by
  unfold finQuotF Binary.round unitsResultF
  simp only []
  rw [roundUnits_reduceF]
  simp [overflowToInfinity]

/-- `sigF` is positive on a nonzero pattern. -/
theorem sigF_pos (f : Format) (b : BitVec f.k) (hb0 : ¬ isZeroF f b) : 0 < sigF f b := by
  have hB := Nat.two_pow_pos f.t
  unfold sigF
  unfold isZeroF at hb0
  by_cases h : expF f b = 0
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- **The certificate bridge, for every format** (`cert16_bridge` for all `Format`s): for
finite nonzero operands, `finQuotF a b` (hence, by `divide_table`, `divide f .nearestTiesToEven a b`)
is exactly the pattern the certificate `certF` accepts. Only `b ≠ 0` is used (`D > 0`). -/
theorem certF_bridge (f : Format) (a b c : BitVec f.k) (hb0 : ¬ isZeroF f b) :
    finQuotF f .nearestTiesToEven a b = c ↔ certF f a b c = true := by
  have hD : 0 < sigF f b * 2 ^ (-(qexpF f a - qexpF f b + f.scale)).toNat :=
    Nat.mul_pos (sigF_pos f b hb0) (Nat.two_pow_pos _)
  rw [finQuotF_eq]
  exact certNF_iff f _ _ hD _ c

end LeanModels.SoftFloat.Binary
