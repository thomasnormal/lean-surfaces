import LeanModels.SoftFloat.Basic

/-!
# IEEE 754-2019 binary interchange formats, on bit patterns: the definitions

The bit-level layer of the family's IEEE 754 component (`docs/family-architecture.md` §3.5): a binary format given
by its exponent width and precision, the encoding of a datum as a `k`-bit string (§3.4), its classification
(§5.7.2), its exact value (§3.3), correct rounding of an exact magnitude under all five rounding-direction
attributes (§4.3, with the overflow results of §7.4 and gradual underflow, §7.5), and `division` (§5.4.1, with the
special cases of §6.1-§6.3, §7.2, §7.3).

Everything is computed on `Nat` (and `Int` for exponents), with `BitVec.toNat`/`BitVec.ofNat` at the boundary: no
floating-point type, no `Rat`, no external code, no recursion. Every definition reduces in the kernel (`decide`).

Shared with the rest of the component (no second notion): the rounding-direction attribute is SoftFloat's
`RoundingMode` (`LeanModels/SoftFloat/Basic.lean`; its constructors spell IEEE's roundTiesToEven, roundTiesToAway,
roundTowardZero, roundTowardPositive, roundTowardNegative as `nearestTiesToEven`, `nearestTiesToAway`, `towardZero`,
`towardPositive`, `towardNegative`), an exact value is also given as SoftFloat's `Q` (`Datum.valueQ`), and a format
maps to core's `Float.Model.Format` (`Format.toCore`, whose `minExponent` is this file's `qmin`).

The definitions are those of svGolf's trusted fdivp specification (`tasks/fdivp/IEEE754.lean`), the same statements
in a language-neutral place; svGolf proves the two equal (`SvGolf/IEEE754Bridge.lean`). This file adds the
classification of §5.7.2, `Datum.valueQ`, `Format.toCore`/`ofCore`, binary128, and `DivisionResult`, the IEEE-level
specification of division that allows every quiet NaN where `divide` picks the canonical one.

NaN policy of `divide` (§6.2.3 says a NaN result *should*, not *shall*, carry an input payload): every NaN result is
the single canonical quiet NaN (sign 0, exponent all ones, trailing significand `10…0`), the RISC-V F/Zfh and
SMT-LIB choice; `DivisionResult` states what IEEE 754 itself requires. Exception flags (§7) are not modelled.
-/

namespace LeanModels.SoftFloat.Binary

export LeanModels.SoftFloat (RoundingMode)

/-! ## Formats (§3.3, §3.4, Table 3.5) -/

/-- A **binary interchange format** (IEEE 754-2019 §3.3, §3.4 and Table 3.5), given by
* `w` — the width in bits of the biased-exponent field `E`, and
* `p` — the precision: the number of significand digits, *including* the implicit leading bit.

binary16 is `w = 5, p = 11`; binary32 is `w = 8, p = 24`; binary64 is `w = 11, p = 53`; binary128 is
`w = 15, p = 113`. The side conditions `2 ≤ w`, `2 ≤ p` exclude degenerate parameter choices (Table 3.5's formats
all satisfy them; with `w = 1` there is no normal number); they are discharged automatically for literals. -/
structure Format where
  /-- Width of the biased-exponent field `E` (§3.4). -/
  w : Nat
  /-- Precision `p`: significand digits including the implicit bit (§3.3). -/
  p : Nat
  hw : 2 ≤ w := by decide
  hp : 2 ≤ p := by decide

namespace Format

variable (f : Format)

/-- `t = p − 1`: width of the trailing significand field `T` (§3.4). -/
abbrev t : Nat := f.p - 1

/-- `k = 1 + w + t`: the storage width in bits (§3.4, Table 3.5). -/
abbrev k : Nat := 1 + f.w + f.t

/-- `emax = 2^(w−1) − 1`, which is also the exponent `bias` (§3.3, §3.4, Table 3.5). -/
def emax : Nat := 2 ^ (f.w - 1) - 1

/-- `emin = 1 − emax` (§3.3). -/
def emin : Int := 1 - (f.emax : Int)

/-- `qmin = emin − (p − 1)`: the least *quantum exponent* (§3.3: a finite number is
`(−1)^s × 2^q × c` with `emin ≤ q + p − 1 ≤ emax`). `2^qmin` is the least positive subnormal
magnitude, and every finite number of the format is an integer multiple of it. -/
def qmin : Int := f.emin - f.t

/-- `scale = −qmin = emax + p − 2` as a natural number: one *unit* `2^qmin = 2^(−scale)` is the
least positive subnormal magnitude (binary16: 24, binary32: 149). Rounding (`round`) works on
magnitudes measured in units, where every finite number of the format is a natural number. -/
def scale : Nat := f.emax + f.t - 1

/-- The largest finite magnitude `(2 − 2^(1−p)) × 2^emax` (§3.3), in units:
`(2^p − 1) × 2^(emax − emin)`. (binary16: `2047 × 2^29` units `= 65504`.) -/
def maxUnits : Nat := (2 ^ f.p - 1) * 2 ^ (2 * f.emax - 1)

/-- The same format as core's record `Float.Model.Format` (`mantissaBitsWithoutImplicit = t`,
`exponentBits = w`), on which SoftFloat's declarative rounding (`ReprQ`, `IsNearest`) and core's `Float.Model` are
stated. -/
def toCore : Float.Model.Format where
  mantissaBitsWithoutImplicit := f.t
  hm := by have := f.hp; show 0 < f.p - 1; omega
  exponentBits := f.w
  he := by have := f.hw; omega

/-- A core format record with at least two exponent bits, as a format of this library. (Core's own record requires
`2 ≤ exponentBits` from Lean v4.35 on; the hypothesis keeps this file buildable on earlier toolchains.) -/
def ofCore (g : Float.Model.Format) (hw : 2 ≤ g.exponentBits) : Format where
  w := g.exponentBits
  p := g.mantissaBitsWithoutImplicit + 1
  hw := hw
  hp := by have := g.hm; omega

/-- The storage width is core's `numBits`. -/
theorem toCore_numBits : f.toCore.numBits = f.k := rfl

/-- The precision is core's `mantissaBits` (the significand with its implicit bit). -/
theorem toCore_mantissaBits : f.toCore.mantissaBits = f.p := by
  have := f.hp
  show 1 + (f.p - 1) = f.p
  omega

/-- `emax`, the bias, is core's `exponentBias`. -/
theorem toCore_exponentBias : f.toCore.exponentBias = f.emax := rfl

/-- **The least quantum exponent `qmin` is core's `minExponent`**: one unit of this library is core's least
exponent step, so a magnitude of `u` units is core's dyadic `u · 2^minExponent` (SoftFloat's `ReprQ` grid). -/
theorem toCore_minExponent : f.toCore.minExponent = f.qmin := by
  have hw := f.hw
  have hp := f.hp
  have h1 : 1 ≤ 2 ^ (f.w - 1) := Nat.one_le_two_pow
  have hc : ((2 ^ (f.w - 1) : Nat) : Int) = (2 : Int) ^ (f.w - 1) := by simp
  simp only [Float.Model.Format.minExponent, Float.Model.Format.mantissaBits, toCore, qmin, emin, emax]
  rw [← hc]
  omega

theorem ofCore_toCore : ofCore f.toCore f.hw = f := by
  obtain ⟨w, p, hw, hp⟩ := f
  simp only [ofCore, toCore, mk.injEq, true_and, Format.t]
  omega

end Format


/-- binary16 (§3.6 Table 3.5: k = 16, p = 11, emax = 15). -/
abbrev binary16 : Format := { w := 5, p := 11 }
/-- binary32 (§3.6 Table 3.5: k = 32, p = 24, emax = 127). -/
abbrev binary32 : Format := { w := 8, p := 24 }
/-- binary64 (§3.6 Table 3.5: k = 64, p = 53, emax = 1023). -/
abbrev binary64 : Format := { w := 11, p := 53 }
/-- binary128 (§3.6 Table 3.5: k = 128, p = 113, emax = 16383). -/
abbrev binary128 : Format := { w := 15, p := 113 }

/-- Core's binary32 and binary64 records are this library's binary32 and binary64. -/
theorem toCore_binary32 : binary32.toCore = Float.Model.Format.binary32 := rfl
theorem toCore_binary64 : binary64.toCore = Float.Model.Format.binary64 := rfl

/-! ## Decoding bit patterns (§3.4) -/

/-- The datum a bit pattern represents (§3.2 levels 2–3, §3.4 (a)–(e)).

* `nan signaling` — a NaN; `signaling` iff the first trailing-significand bit is 0 (§6.2.1).
  The payload is not recorded here (`decode` keeps the pattern; nothing below propagates payloads).
* `inf neg` — `+∞` or `−∞` (`neg = true` means sign bit 1).
* `zero neg` — `+0` or `−0`.
* `finite neg q c` — the nonzero number `(−1)^neg × 2^q × c` in the integral-significand
  notation of §3.3, with `0 < c < 2^p` and `qmin ≤ q`. -/
inductive Datum where
  | nan (signaling : Bool)
  | inf (neg : Bool)
  | zero (neg : Bool)
  | finite (neg : Bool) (q : Int) (c : Nat)
  deriving DecidableEq, Repr

/-- **Decoding** (§3.4, Figure 3.1). The `k`-bit string is `S ‖ E ‖ T`: the sign bit `S`, the
`w`-bit biased exponent `E` and the `t`-bit trailing significand `T`, most significant first.
The five cases are §3.4 (a)–(e), with the significand written as an integer
(`1.T = (2^t + T) × 2^(−t)`, `0.T = T × 2^(−t)`):

* (a) `E = 2^w − 1`, `T ≠ 0`: NaN (quiet iff `T`'s leading bit `d₁` is 1, §6.2.1);
* (b) `E = 2^w − 1`, `T = 0`: `(−1)^S × ∞`;
* (c) `1 ≤ E ≤ 2^w − 2`: `(−1)^S × 2^(E − bias) × (1 + 2^(1−p) × T)
       = (−1)^S × 2^(E − bias − t) × (2^t + T)` — normal;
* (d) `E = 0`, `T ≠ 0`: `(−1)^S × 2^emin × (0 + 2^(1−p) × T) = (−1)^S × 2^(emin − t) × T`
       — subnormal;
* (e) `E = 0`, `T = 0`: `(−1)^S × 0`. -/
def decode (f : Format) (x : BitVec f.k) : Datum :=
  let S := x.toNat / 2 ^ (f.w + f.t)
  let E := x.toNat / 2 ^ f.t % 2 ^ f.w
  let T := x.toNat % 2 ^ f.t
  let neg := S == 1
  if E = 2 ^ f.w - 1 then
    if T = 0 then .inf neg                                   -- (b)
    else .nan (T < 2 ^ (f.t - 1))                            -- (a): signaling iff d₁ = 0
  else if E = 0 then
    if T = 0 then .zero neg                                  -- (e)
    else .finite neg (f.emin - f.t) T                        -- (d) subnormal
  else .finite neg ((E : Int) - f.emax - f.t) (2 ^ f.t + T)  -- (c) normal, bias = emax

/-- The **exact value** of a datum as a fraction `num / den` of an integer and a positive
natural number (§3.3: the finite number `(−1)^neg × 2^q × c`; zeros have value 0). NaNs and
infinities have no real value (`none`). The fraction is not reduced; `den` is a power of 2. -/
def Datum.value? : Datum → Option (Int × Nat)
  | .zero _ => some (0, 1)
  | .finite neg q c =>
    let num : Int := c * 2 ^ q.toNat
    some (if neg then -num else num, 2 ^ (-q).toNat)
  | .nan _ | .inf _ => none

/-- The exact value as SoftFloat's rational `Q` (the same fraction as `value?`; its denominator is a power of 2,
hence positive). -/
def Datum.valueQ : Datum → Option Q
  | .zero _ => some ⟨0, 1, Nat.one_pos⟩
  | .finite neg q c =>
    let num : Int := c * 2 ^ q.toNat
    some ⟨if neg then -num else num, 2 ^ (-q).toNat, Nat.two_pow_pos _⟩
  | .nan _ | .inf _ => none

theorem Datum.valueQ_eq (d : Datum) :
    d.valueQ.map (fun q => (q.num, q.den)) = d.value? := by
  cases d <;> rfl

/-! ## Classification (§5.7.2) -/

/-- The ten classes of §5.7.2 `class(x)`. -/
inductive Class where
  | signalingNaN
  | quietNaN
  | negativeInfinity
  | negativeNormal
  | negativeSubnormal
  | negativeZero
  | positiveZero
  | positiveSubnormal
  | positiveNormal
  | positiveInfinity
  deriving DecidableEq, Repr

/-- `class(x)` (§5.7.2), read from the fields (§3.4): `E = 2^w − 1` is a NaN or an infinity, `E = 0` a zero or a
subnormal, anything else a normal number; the sign bit gives the sign of every non-NaN class. -/
def classify (f : Format) (x : BitVec f.k) : Class :=
  match decode f x with
  | .nan true => .signalingNaN
  | .nan false => .quietNaN
  | .inf true => .negativeInfinity
  | .inf false => .positiveInfinity
  | .zero true => .negativeZero
  | .zero false => .positiveZero
  | .finite neg _ _ =>
    if x.toNat / 2 ^ f.t % 2 ^ f.w = 0 then (if neg then .negativeSubnormal else .positiveSubnormal)
    else (if neg then .negativeNormal else .positiveNormal)

/-- §5.7.2 `isSignMinus(x)`: the sign bit is 1 (for every datum, NaNs included). -/
def isSignMinus (f : Format) (x : BitVec f.k) : Bool := x.toNat / 2 ^ (f.w + f.t) == 1
/-- §5.7.2 `isNormal(x)`. -/
def isNormal (f : Format) (x : BitVec f.k) : Bool :=
  classify f x == .negativeNormal || classify f x == .positiveNormal
/-- §5.7.2 `isSubnormal(x)`. -/
def isSubnormal (f : Format) (x : BitVec f.k) : Bool :=
  classify f x == .negativeSubnormal || classify f x == .positiveSubnormal
/-- §5.7.2 `isZero(x)`. -/
def isZero (f : Format) (x : BitVec f.k) : Bool :=
  classify f x == .negativeZero || classify f x == .positiveZero
/-- §5.7.2 `isInfinite(x)`. -/
def isInfinite (f : Format) (x : BitVec f.k) : Bool :=
  classify f x == .negativeInfinity || classify f x == .positiveInfinity
/-- §5.7.2 `isNaN(x)`. -/
def isNaN (f : Format) (x : BitVec f.k) : Bool :=
  classify f x == .signalingNaN || classify f x == .quietNaN
/-- §5.7.2 `isSignaling(x)`. -/
def isSignaling (f : Format) (x : BitVec f.k) : Bool := classify f x == .signalingNaN
/-- §5.7.2 `isFinite(x)`: zero, subnormal or normal. -/
def isFinite (f : Format) (x : BitVec f.k) : Bool := !(isInfinite f x || isNaN f x)

/-! ## Encoding (§3.4) -/

/-- The `k`-bit string `S ‖ E ‖ T` (§3.4, Figure 3.1) for sign `neg`, biased exponent `E < 2^w`
and trailing significand `T < 2^t`. -/
def fields (f : Format) (neg : Bool) (E T : Nat) : BitVec f.k :=
  BitVec.ofNat f.k ((if neg then 1 else 0) * 2 ^ (f.w + f.t) + E * 2 ^ f.t + T)

/-- `(−1)^neg × ∞`: `E = 2^w − 1`, `T = 0` (§3.4 (b)). -/
def infinity (f : Format) (neg : Bool) : BitVec f.k := fields f neg (2 ^ f.w - 1) 0

/-- `(−1)^neg × 0`, a signed zero: `E = 0`, `T = 0` (§3.4 (e)). -/
def zero (f : Format) (neg : Bool) : BitVec f.k := fields f neg 0 0

/-- **The canonical NaN** (the NaN policy of `divide`, §6.2.1, §6.2.3): sign 0,
`E = 2^w − 1`, `T = 2^(t−1)` — a quiet NaN (`d₁ = 1`) with all other payload bits 0.
binary16: `0x7E00`; binary32: `0x7FC00000`. -/
def canonicalNaN (f : Format) : BitVec f.k := fields f false (2 ^ f.w - 1) (2 ^ (f.t - 1))

/-- `(−1)^neg × u × 2^qmin`, i.e. the finite magnitude of `u` units, encoded (§3.4 (c)–(e)).
Precondition: `u` is a representable magnitude — `u = c × 2^j` with `c < 2^p` — and
`u ≤ maxUnits`; `round` only produces such `u`.

* `u < 2^t`: a subnormal or zero, `E = 0`, `T = u` (§3.4 (d), (e)).
* otherwise `u = c × 2^j` with `2^t ≤ c < 2^p`, `j = ⌊log₂ u⌋ − t`; this is the normal number
  `2^(qmin + j) × c` with biased exponent `E = j + 1` and `T = c − 2^t` (§3.4 (c)). -/
def finite (f : Format) (neg : Bool) (u : Nat) : BitVec f.k :=
  if u < 2 ^ f.t then fields f neg 0 u
  else
    let j := Nat.log2 u - f.t
    fields f neg (j + 1) (u / 2 ^ j - 2 ^ f.t)

/-! ## Rounding (§4.3, §5.4.1, §7.4) -/

/-- The spacing exponent of representable magnitudes near a magnitude of `n` units: in the
binade `[2^(p−1+j), 2^(p+j))` units (`j ≥ 1`), the representable magnitudes are exactly the
multiples of `2^j` units (§3.3: `2^q × c` with `q = qmin + j`, `2^(p−1) ≤ c < 2^p`); below
`2^p` units (subnormals and the lowest normal binade) they are the multiples of 1 unit.
Computed as `max(0, ⌊log₂ n⌋ + 1 − p)` (`Nat` subtraction truncates at 0; `log2 0 = 0`).
There is no upper limit on `j`: this is the *unbounded exponent range* of §4.3 and §7.4. -/
def ulpExp (f : Format) (n : Nat) : Nat := (Nat.log2 n + 1) - f.p

/-- **Rounding with unbounded exponent range** (§4.3, and §7.4's "rounded … were the exponent
range unbounded") of the exact magnitude `N / D` units (`D > 0`), with `neg` the sign of the
exact result (it matters only for the directed attributes).

`N / D` lies in the binade of `⌊N/D⌋` (binade boundaries are integers), where representable
magnitudes are the multiples of `2^j` units, `j = ulpExp ⌊N/D⌋`. Write `M = D × 2^j` and
`N = c × M + r` with `0 ≤ r < M`; then `N/D = (c + r/M) × 2^j`, so `c × 2^j` and `(c + 1) × 2^j`
are the two representable magnitudes bracketing `N/D` (`(c+1) × 2^j` may be `2^p × 2^j`, which
is `2^(p−1) × 2^(j+1)`), and `2r` versus `M` compares the distance to them:

* roundTiesToEven (§4.3.1): the nearer; on a tie (`2r = M`) the one with even significand
  — `c × 2^j` iff `c` is even;
* roundTiesToAway (§4.3.1): the nearer; on a tie the larger magnitude;
* roundTowardPositive / roundTowardNegative / roundTowardZero (§4.3.2): the one in that direction
  (for a magnitude: up iff inexact and the direction points away from zero).

The result is a magnitude in units. `IsRoundedTo` (`Round.lean`) states the same declaratively. -/
def roundUnits (f : Format) (mode : RoundingMode) (neg : Bool) (N D : Nat) : Nat :=
  let j := ulpExp f (N / D)
  let M := D * 2 ^ j
  let c := N / M
  let r := N % M
  let up : Bool :=
    match mode with
    | .nearestTiesToEven => 2 * r > M || (2 * r == M && c % 2 == 1)
    | .nearestTiesToAway => 2 * r ≥ M
    | .towardPositive => r != 0 && !neg
    | .towardNegative => r != 0 && neg
    | .towardZero => false
  (if up then c + 1 else c) * 2 ^ j

/-- Whether an overflow delivers `∞` (rather than the largest finite magnitude) — §7.4:
roundTiesToEven and roundTiesToAway carry all overflows to `∞`; roundTowardZero carries all
overflows to the largest finite number; roundTowardPositive carries negative overflows to the
most negative finite number and positive overflows to `+∞`; roundTowardNegative the mirror. -/
def overflowToInfinity : RoundingMode → (neg : Bool) → Bool
  | .nearestTiesToEven, _ => true
  | .nearestTiesToAway, _ => true
  | .towardZero, _ => false
  | .towardPositive, neg => !neg
  | .towardNegative, neg => neg

/-- **The correctly rounded result** (§4.3, §5.4.1, §7.4, §7.5) of the exact nonzero value
`(−1)^neg × n / d` (`n, d > 0`), as a bit pattern of format `f`:

1. measure the magnitude in units of `2^qmin`: `n / d = (n × 2^scale / d) × 2^qmin`;
2. round it with unbounded exponent range (`roundUnits`); results below the normal range are
   subnormals or zero — gradual underflow, no flush-to-zero (§3.3, §7.5);
3. if the rounded magnitude exceeds the largest finite magnitude, the operation overflows
   (§7.4) and delivers `±∞` or `±maxFinite` per `overflowToInfinity`; otherwise it is encoded
   with sign `neg` — a zero result keeps the sign `neg` (§6.3).

Every operation whose exact result is a nonzero rational (`+ − × ÷`, conversions) ends here. -/
def round (f : Format) (mode : RoundingMode) (neg : Bool) (n d : Nat) : BitVec f.k :=
  let u := roundUnits f mode neg (n * 2 ^ f.scale) d
  if u ≤ f.maxUnits then finite f neg u
  else if overflowToInfinity mode neg then infinity f neg
  else finite f neg f.maxUnits

/-! ## Division (§5.4.1) -/

/-- **IEEE 754-2019 division** `division(x, y)` (§5.4.1) of format `f` under rounding-direction
attribute `mode`, on bit patterns.

The special cases, in order:
* any NaN operand (quiet or signaling) → the canonical NaN (§6.2, the NaN policy above);
* `division(∞, ∞)` and `division(0, 0)` are invalid operations (§7.2) → the canonical NaN;
* `division(∞, y)` for finite `y`, zero included → `∞`, exact (§6.1);
* `division(x, ∞)` for finite `x`, zero included → `0`, exact (§6.1);
* `division(x, 0)` for finite nonzero `x` → `∞`, the divideByZero exception (§7.3);
* `division(0, y)` for finite nonzero `y` → `0`, exact.
In all non-NaN cases the sign of the result is the exclusive OR of the operands' signs (§6.3).

Otherwise `x = (−1)^sx × 2^qx × cx` and `y = (−1)^sy × 2^qy × cy` are finite nonzero, and the
result is the exact quotient rounded (§4.3, §5.1: as if computed with unbounded range and
precision, then rounded): `|x| / |y| = (nx / dx) / (ny / dy) = (nx × dy) / (dx × ny)`
where `nx / dx` is `|x|` as a fraction (`Datum.value?`). -/
def divide (f : Format) (mode : RoundingMode) (a b : BitVec f.k) : BitVec f.k :=
  match decode f a, decode f b with
  | .nan _, _ | _, .nan _ => canonicalNaN f
  | .inf _, .inf _ => canonicalNaN f
  | .zero _, .zero _ => canonicalNaN f
  | .inf sx, .zero sy | .inf sx, .finite sy _ _ => infinity f (sx ^^ sy)
  | .zero sx, .inf sy | .finite sx _ _, .inf sy => zero f (sx ^^ sy)
  | .finite sx _ _, .zero sy => infinity f (sx ^^ sy)
  | .zero sx, .finite sy _ _ => zero f (sx ^^ sy)
  | .finite sx qx cx, .finite sy qy cy =>
    -- |x| = nx / dx and |y| = ny / dy exactly (Datum.value? without the sign)
    let nx := cx * 2 ^ qx.toNat
    let dx := 2 ^ (-qx).toNat
    let ny := cy * 2 ^ qy.toNat
    let dy := 2 ^ (-qy).toNat
    round f mode (sx ^^ sy) (nx * dy) (dx * ny)

/-- **What IEEE 754-2019 requires of `division(x, y)`**, where it leaves a choice open: the result `r` is
`divide f mode a b` whenever that is not a NaN, and any QUIET NaN otherwise. A NaN result is always quiet (§6.2:
an operation on quiet NaNs delivers a quiet NaN; §7.2: an invalid operation, signaling NaN operands included,
delivers a quiet NaN), its sign is not interpreted (§6.3) and its payload *should* be an input's (§6.2.3), so every
quiet NaN is admitted. `divide`'s canonical NaN is one resolution (`divide_isResult`, `Characterization.lean`); a
theorem about a divider that may produce another NaN is stated with this predicate. -/
def DivisionResult (f : Format) (mode : RoundingMode) (a b r : BitVec f.k) : Prop :=
  (∀ s, decode f (divide f mode a b) ≠ .nan s) ∧ r = divide f mode a b ∨
  (∃ s, decode f (divide f mode a b) = .nan s) ∧ decode f r = .nan false

/-- The binary16 instance: binary16 division, roundTiesToEven. -/
def divBinary16 (a b : BitVec 16) : BitVec 16 := divide binary16 .nearestTiesToEven a b

/-- The binary32 instance: binary32 division, roundTiesToEven. -/
def divBinary32 (a b : BitVec 32) : BitVec 32 := divide binary32 .nearestTiesToEven a b

end LeanModels.SoftFloat.Binary
