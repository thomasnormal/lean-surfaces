/-
# SoftFloat, layer 2 — the SPEC ALGEBRA

`docs/family-architecture.md` §3.5.1.  The spec half: nothing in this file
mentions core's `UnpackedFloat` operations, so every statement here survives a
definition swap (`docs/statement-cookbook.md` §6).  ℝ never appears: the exact
value of every `+ − × ÷ √ fma` on finite inputs is a RATIONAL, and rounding a
rational to a format is finite integer arithmetic (§3.5.1).

WIDTH-PARAMETRICITY IS A REQUIREMENT (§3.5.1, three clauses): everything below
is defined over a general `Float.Model.Format`; `binary16/32/64/128` are
INSTANCES, never separate definitions.

TERMINATION / FUEL.  There is none, and that is a decision, not an omission:
every function here is a composition of total `Int`/`Nat` operations with no
recursion of its own.  Rounding a rational to a format is `Nat.log2`, a shift
and a division; it does not search.  So no fuel parameter, no well-founded
recursion, and — the reason it matters — everything is KERNEL-REDUCIBLE, which
is what lets the base cases close by `decide` (§0.1 II(a) rung 2).
-/
import Init.Data.Float.Model

namespace LeanModels.SoftFloat

open Float.Model
open Float.Model.UnpackedFloat (Sign)

/-! ## 1 `Q` — the exact value, as a rational

IEEE 754-2019 §3.2 speaks of the "infinitely precise" result.  For the five
algebraic operations on finite inputs that value is rational, so `Q` is all the
number system this component needs.  Not normalized: comparison is by
cross-multiplication, which keeps every operation in `Int`.
-/

/-- An exact value `num / den`, with `den > 0`.  Not normalized. -/
structure Q where
  /-- The numerator. -/
  num : Int
  /-- The denominator; always positive. -/
  den : Nat
  /-- The denominator is positive. -/
  den_pos : 0 < den
deriving Repr

namespace Q

/-- The exact value of an integer. -/
def ofInt (n : Int) : Q := ⟨n, 1, Nat.one_pos⟩

instance : OfNat Q 0 := ⟨ofInt 0⟩
instance : OfNat Q 1 := ⟨ofInt 1⟩

/-- The exact value `m * 2 ^ e`.  Every finite float's value has this shape. -/
def dyadic (m : Int) (e : Int) : Q :=
  if 0 ≤ e then ⟨m * 2 ^ e.toNat, 1, Nat.one_pos⟩
  else ⟨m, 2 ^ (-e).toNat, Nat.two_pow_pos _⟩

/-- Exact negation. -/
protected def neg (a : Q) : Q := ⟨-a.num, a.den, a.den_pos⟩

/-- Exact addition. -/
protected def add (a b : Q) : Q :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

/-- Exact subtraction. -/
protected def sub (a b : Q) : Q := Q.add a (Q.neg b)

/-- Exact multiplication. -/
protected def mul (a b : Q) : Q :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

/--
Exact division.  A zero divisor has NO exact quotient — IEEE 754-2019 §7.3
routes division by zero through the special-value table and the `divideByZero`
exception — so the result is `Option`, exactly as `valQ` is `Option` for the
values that do not denote a real number.  A sentinel here would be the silent
degrade the family forbids.
-/
protected def div (a b : Q) : Option Q :=
  if h : b.num = 0 then none
  else some ⟨a.num * b.den * b.num.sign, a.den * b.num.natAbs,
    Nat.mul_pos a.den_pos (Int.natAbs_pos.mpr h)⟩

instance : Neg Q := ⟨Q.neg⟩
instance : Add Q := ⟨Q.add⟩
instance : Sub Q := ⟨Q.sub⟩
instance : Mul Q := ⟨Q.mul⟩

/-- Compare two exact values, by cross-multiplication.  Stays in `Int`. -/
protected def compare (a b : Q) : Ordering := compare (a.num * b.den) (b.num * a.den)

instance : Ord Q := ⟨Q.compare⟩

/-- Exact equality (not structural: `1/2` and `2/4` are equal here). -/
protected def beq (a b : Q) : Bool := a.num * b.den == b.num * a.den

/--
Truncation toward zero: IEEE 754-2019 §5.8 `convertToIntegerTowardZero`.
`Int.tdiv` is truncating division, which is what "toward zero" means.
-/
def truncate (a : Q) : Int := a.num.tdiv a.den

/-- The sign of an exact value, as an `Int` in `{-1, 0, 1}`. -/
def sign (a : Q) : Int := a.num.sign

end Q

/-! ## 2 `valQ` — what a float MEANS

IEEE 754-2019 §3.2: only finite floats denote a real number.  NaN and the
infinities have no exact value, and saying so with `Option` rather than with a
sentinel is what keeps the specification loud (`AGENTS.md`: never hide errors).
-/

/-- The exact value of an `UnpackedFloat`, or `none` for NaN and the infinities. -/
def valQ : UnpackedFloat → Option Q
  | .notANumber => none
  | .infinity _ => none
  | .zero _ => some 0
  | .finite s m e _ => some (Q.dyadic (s.apply m) e)

/-! ## 3 Rounding — IEEE 754-2019 §4.3, ALL FIVE attributes

Core implements exactly one of these (`Accuracy.roundToNearestEven`; measured,
see `docs/softfloat-charter.md` §1).  The spec carries all five from the first
commit for the same reason the format is a parameter: a spec that names one
mode has hard-coded the default the way a spec that names one width hard-codes
binary64.
-/

/-- IEEE 754-2019 §4.3: the rounding-direction attributes. -/
inductive RoundingMode where
  /-- §4.3.1 roundTiesToEven — the default for binary formats (§4.3.3). -/
  | nearestTiesToEven
  /-- §4.3.1 roundTiesToAway. -/
  | nearestTiesToAway
  /-- §4.3.2 roundTowardZero. -/
  | towardZero
  /-- §4.3.2 roundTowardPositive. -/
  | towardPositive
  /-- §4.3.2 roundTowardNegative. -/
  | towardNegative
deriving DecidableEq, Repr, BEq

/-! ## 4 Exceptions — IEEE 754-2019 §7, as a payload and never silent -/

/--
IEEE 754-2019 §7: the five exceptions.  Carried as a VERDICT-CLASS payload
(`docs/family-architecture.md` §5.2) rather than raised, because a tier that
does not model flags must be able to ignore them without the model pretending
they did not occur.
-/
inductive Exception where
  /-- §7.2 invalid operation. -/
  | invalid
  /-- §7.3 division by zero. -/
  | divideByZero
  /-- §7.4 overflow. -/
  | overflow
  /-- §7.5 underflow. -/
  | underflow
  /-- §7.6 inexact. -/
  | inexact
deriving DecidableEq, Repr, BEq


open Float.Model.UnpackedFloat (Sign ExtendedMantissa Accuracy)

end LeanModels.SoftFloat
