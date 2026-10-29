import LeanModels.Core.Basic
import Lean.ToExpr

namespace LeanModels.Python

structure Float64 where
  bits : UInt64
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace Float64

def ofBits (bits : Nat) : Float64 := ⟨UInt64.ofNat bits⟩

def sign (value : Float64) : Bool := value.bits.toNat ≥ 2 ^ 63

def exponent (value : Float64) : Nat := value.bits.toNat / 2 ^ 52 % 2048

def fraction (value : Float64) : Nat := value.bits.toNat % 2 ^ 52

def isNaN (value : Float64) : Bool :=
  value.exponent == 2047 && value.fraction != 0

def isInf (value : Float64) : Bool :=
  value.exponent == 2047 && value.fraction == 0

def isZero (value : Float64) : Bool := value.bits.toNat % 2 ^ 63 == 0

def neg (value : Float64) : Float64 :=
  ofBits ((if value.sign then 0 else 2 ^ 63) + value.bits.toNat % 2 ^ 63)

def abs (value : Float64) : Float64 := ofBits (value.bits.toNat % 2 ^ 63)

private def scaleBinary (numerator denominator : Nat) (power : Int) : Nat × Nat :=
  if power ≥ 0 then (numerator, denominator * 2 ^ power.toNat)
  else (numerator * 2 ^ (-power).toNat, denominator)

private def roundEven (numerator denominator : Nat) : Nat :=
  let quotient := numerator / denominator
  let remainder := numerator % denominator
  if 2 * remainder < denominator then quotient
  else if 2 * remainder > denominator then quotient + 1
  else if quotient % 2 == 0 then quotient else quotient + 1

private def binaryExponent (numerator denominator : Nat) : Int :=
  let estimate := (numerator.log2 : Int) - (denominator.log2 : Int)
  let (scaledNumerator, scaledDenominator) := scaleBinary numerator denominator estimate
  if scaledNumerator < scaledDenominator then estimate - 1 else estimate

def fromRatio (negative : Bool) (numerator denominator : Nat) : Option Float64 :=
  if denominator == 0 then none
  else
    let signBits := if negative then 2 ^ 63 else 0
    if numerator == 0 then some (ofBits signBits)
    else
      let power := max (-1074) (binaryExponent numerator denominator - 52)
      let (scaledNumerator, scaledDenominator) := scaleBinary numerator denominator power
      let significand := roundEven scaledNumerator scaledDenominator
      let (significand, power) :=
        if significand ≥ 2 ^ 53 then (significand / 2, power + 1)
        else (significand, power)
      let biasedExponent := (power + 1075).toNat
      let magnitude :=
        if significand < 2 ^ 52 then significand
        else if biasedExponent ≥ 2047 then 2047 * 2 ^ 52
        else biasedExponent * 2 ^ 52 + significand - 2 ^ 52
      some (ofBits (signBits + magnitude))

inductive DivisionError where
  | zeroDivision
  | overflow
deriving Repr, BEq, DecidableEq, Lean.ToExpr

def divideInt (left right : Int) : Except DivisionError Float64 :=
  if right == 0 then .error .zeroDivision
  else
    match fromRatio ((left < 0) != (right < 0)) left.natAbs right.natAbs with
    | none => .error .zeroDivision
    | some value => if value.isInf then .error .overflow else .ok value

private def magnitudeRatio (value : Float64) : Nat × Nat :=
  let significand := if value.exponent == 0 then value.fraction else 2 ^ 52 + value.fraction
  let power := if value.exponent == 0 then -1074 else (value.exponent : Int) - 1075
  if power ≥ 0 then (significand * 2 ^ power.toNat, 1)
  else (significand, 2 ^ (-power).toNat)

def toRatio (value : Float64) : Option (Int × Nat) :=
  if value.exponent == 2047 then none
  else
    let (numerator, denominator) := value.magnitudeRatio
    some (if value.sign then -(numerator : Int) else (numerator : Int), denominator)

/-- Reduce an exact binary64 ratio to the canonical positive-denominator
    representative used by Python's numeric key equality. -/
def normalizeRatio (ratio : Int × Nat) : Int × Nat :=
  let g := ratio.1.natAbs.gcd ratio.2
  if g == 0 then ratio
  else (ratio.1 / (g : Int), ratio.2 / g)

def keyRatio (value : Float64) : Option (Int × Nat) :=
  value.toRatio.map normalizeRatio

def eqv (left right : Float64) : Bool :=
  !left.isNaN && !right.isNaN &&
    (left.bits == right.bits || left.isZero && right.isZero)

def eqInt (value : Float64) (integer : Int) : Bool :=
  match value.toRatio with
  | none => false
  | some (numerator, denominator) => numerator == integer * (denominator : Int)

def lt (left right : Float64) : Bool :=
  if left.isNaN || right.isNaN || left.eqv right then false
  else if left.sign != right.sign then left.sign
  else if left.sign then right.bits.toNat < left.bits.toNat
  else left.bits.toNat < right.bits.toNat

def ltInt (value : Float64) (integer : Int) : Bool :=
  if value.isNaN then false
  else if value.isInf then value.sign
  else
    match value.toRatio with
    | none => false
    | some (numerator, denominator) => numerator < integer * (denominator : Int)

def intLt (integer : Int) (value : Float64) : Bool :=
  if value.isNaN then false
  else if value.isInf then !value.sign
  else
    match value.toRatio with
    | none => false
    | some (numerator, denominator) => integer * (denominator : Int) < numerator

def fromInt (integer : Int) : Option Float64 :=
  match fromRatio (integer < 0) integer.natAbs 1 with
  | none => none
  | some value => if value.isInf then none else some value

inductive TextError where
  | invalid
  | nanPayload
deriving Repr, BEq, DecidableEq, Lean.ToExpr

def decimalZeroes : List Nat :=
  [0x30, 0x660, 0x6f0, 0x7c0, 0x966, 0x9e6, 0xa66, 0xae6, 0xb66,
   0xbe6, 0xc66, 0xce6, 0xd66, 0xde6, 0xe50, 0xed0, 0xf20, 0x1040,
   0x1090, 0x17e0, 0x1810, 0x1946, 0x19d0, 0x1a80, 0x1a90, 0x1b50,
   0x1bb0, 0x1c40, 0x1c50, 0xa620, 0xa8d0, 0xa900, 0xa9d0, 0xa9f0,
   0xaa50, 0xabf0, 0xff10, 0x104a0, 0x10d30, 0x11066, 0x110f0,
   0x11136, 0x111d0, 0x112f0, 0x11450, 0x114d0, 0x11650, 0x116c0,
   0x11730, 0x118e0, 0x11950, 0x11c50, 0x11d50, 0x11da0, 0x16a60,
   0x16b50, 0x1d7ce, 0x1d7d8, 0x1d7e2, 0x1d7ec, 0x1d7f6, 0x1e140,
   0x1e2f0, 0x1e950, 0x1fbf0]

private def numericWhitespace (character : Char) : Bool :=
  character == ' ' || character == '\t' || character == '\n' ||
    character == '\r' || character.toNat == 0x0b || character.toNat == 0x0c

def normalizeDecimalChar (character : Char) : Char :=
  let code := character.toNat
  if code < 128 then character
  else if code == 0x85 || code == 0xa0 || code == 0x1680 ||
      (0x2000 ≤ code && code ≤ 0x200a) || code == 0x2028 || code == 0x2029 ||
      code == 0x202f || code == 0x205f || code == 0x3000 then ' '
  else
    match decimalZeroes.find? (fun first => first ≤ code && code < first + 10) with
    | some first => Char.ofNat (48 + code - first)
    | none => character

private structure DecimalDigits where
  value : Nat := 0
  count : Nat := 0
  significant : Nat := 0

private def scanDecimal : List Char → DecimalDigits → Bool →
    Option (DecimalDigits × List Char)
  | [], digits, previousDigit =>
      if digits.count == 0 || previousDigit then some (digits, []) else none
  | character :: rest, digits, previousDigit =>
      if character.isDigit then
        let digit := character.toNat - 48
        scanDecimal rest
          ⟨digits.value * 10 + digit, digits.count + 1,
           if digits.significant == 0 && digit == 0 then 0 else digits.significant + 1⟩ true
      else if character == '_' then
        if previousDigit then scanDecimal rest digits false else none
      else if digits.count == 0 || previousDigit then some (digits, character :: rest)
      else none

private def signedDecimal (characters : List Char) : Option Int := do
  let (negative, characters) := match characters with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | _ => (false, characters)
  let (digits, rest) ← scanDecimal characters {} false
  if digits.count == 0 || !rest.isEmpty then none
  else some (if negative then -(digits.value : Int) else (digits.value : Int))

private def decimalRatio (characters : List Char) : Option (Nat × Nat × Int) := do
  let (whole, rest) ← scanDecimal characters {} false
  let (fractional, rest) ← match rest with
    | '.' :: rest => scanDecimal rest {} false
    | _ => some ({}, rest)
  if whole.count + fractional.count == 0 then none
  else
    let power ← match rest with
      | [] => some 0
      | 'e' :: rest => signedDecimal rest
      | 'E' :: rest => signedDecimal rest
      | _ => none
    let significant := if whole.significant == 0 then fractional.significant
      else whole.significant + fractional.count
    some (whole.value * 10 ^ fractional.count + fractional.value, significant,
      power - (fractional.count : Int))

def fromText (text : String) : Except TextError Float64 :=
  let characters := text.toList.map normalizeDecimalChar
  let characters := ((characters.dropWhile numericWhitespace).reverse.dropWhile numericWhitespace).reverse
  let (negative, characters) := match characters with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | _ => (false, characters)
  let folded := characters.map fun character =>
    if 65 ≤ character.toNat && character.toNat ≤ 90 then Char.ofNat (character.toNat + 32)
    else character
  let signBits := if negative then 2 ^ 63 else 0
  if folded == ['i', 'n', 'f'] || folded == ['i', 'n', 'f', 'i', 'n', 'i', 't', 'y'] then
    .ok (ofBits (signBits + 2047 * 2 ^ 52))
  else if folded == ['n', 'a', 'n'] then
    -- CPython's textual NaN constructor uses the canonical quiet-NaN word;
    -- preserve only its explicit sign here. Arithmetic NaN payload/sign
    -- propagation remains a separate unresolved operation.
    .ok (ofBits (signBits + 2047 * 2 ^ 52 + 2 ^ 51))
  else
    match decimalRatio characters with
    | none => .error .invalid
    | some (coefficient, significant, power) =>
      if coefficient == 0 then .ok (ofBits signBits)
      else
        let order := (significant : Int) - 1 + power
        if order > 308 then .ok (ofBits (signBits + 2047 * 2 ^ 52))
        else if order < -324 then .ok (ofBits signBits)
        else
          let (numerator, denominator) := if power ≥ 0 then
            (coefficient * 10 ^ power.toNat, 1)
          else (coefficient, 10 ^ (-power).toNat)
          match fromRatio negative numerator denominator with
          | some value => .ok value
          | none => .error .invalid

def toInt (value : Float64) : Option Int :=
  match value.toRatio with
  | none => none
  | some (numerator, denominator) =>
      let magnitude := numerator.natAbs / denominator
      some (if numerator < 0 then -(magnitude : Int) else (magnitude : Int))

def toIntegralInt (value : Float64) : Option Int :=
  match value.toRatio with
  | none => none
  | some (numerator, denominator) =>
      if numerator % (denominator : Int) == 0 then value.toInt else none

inductive ArithmeticOp where
  | add
  | sub
  | mult
deriving Repr, BEq, DecidableEq, Lean.ToExpr

inductive ArithmeticError where
  | conversionOverflow
  | nanPayload
deriving Repr, BEq, DecidableEq, Lean.ToExpr

private def addSub (subtract : Bool) (left right : Float64) : Except ArithmeticError Float64 :=
  if left.isNaN || right.isNaN then .error .nanPayload
  else
    let rightNegative := right.sign != subtract
    if left.isInf then
      if right.isInf && left.sign != rightNegative then .error .nanPayload
      else .ok left
    else if right.isInf then .ok (if subtract then right.neg else right)
    else
      let (leftMagnitude, leftDenominator) := left.magnitudeRatio
      let (rightMagnitude, rightDenominator) := right.magnitudeRatio
      let leftNumerator : Int := if left.sign then -(leftMagnitude : Int) else leftMagnitude
      let rightNumerator : Int := if right.sign then -(rightMagnitude : Int) else rightMagnitude
      let numerator :=
        if subtract then leftNumerator * rightDenominator - rightNumerator * leftDenominator
        else leftNumerator * rightDenominator + rightNumerator * leftDenominator
      let negative := numerator < 0 || numerator == 0 && left.sign && rightNegative
      match fromRatio negative numerator.natAbs (leftDenominator * rightDenominator) with
      | none => .error .nanPayload
      | some value => .ok value

private def multiply (left right : Float64) : Except ArithmeticError Float64 :=
  if left.isNaN || right.isNaN then .error .nanPayload
  else if left.isInf && right.isZero || right.isInf && left.isZero then .error .nanPayload
  else
    let negative := left.sign != right.sign
    if left.isInf || right.isInf then
      .ok (ofBits ((if negative then 2 ^ 63 else 0) + 2047 * 2 ^ 52))
    else
      let (leftNumerator, leftDenominator) := left.magnitudeRatio
      let (rightNumerator, rightDenominator) := right.magnitudeRatio
      match fromRatio negative (leftNumerator * rightNumerator)
          (leftDenominator * rightDenominator) with
      | none => .error .nanPayload
      | some value => .ok value

def arithmetic (operator : ArithmeticOp) (left right : Float64) : Except ArithmeticError Float64 :=
  match operator with
  | .add => addSub false left right
  | .sub => addSub true left right
  | .mult => multiply left right

/-- CPython 3.9's pinned binary64 NaN propagation: an input NaN is quieted
in place and the left operand wins when both operands are NaN. Invalid
infinite/zero combinations use the canonical negative quiet-NaN word
observed on the same platform. The existing `arithmetic` worker keeps its
`nanPayload` marker for callers that still require an explicit oracle. -/
def quietNaN (value : Float64) : Float64 :=
  ofBits (value.bits.toNat ||| 2 ^ 51)

def arithmeticWithNaN (operator : ArithmeticOp) (left right : Float64) :
    Except ArithmeticError Float64 :=
  if left.isNaN then .ok (quietNaN left)
  else if right.isNaN then .ok (quietNaN right)
  else
    match arithmetic operator left right with
    | .ok value => .ok value
    | .error .nanPayload => .ok (ofBits 0xfff8000000000000)
    | .error .conversionOverflow => .error .conversionOverflow


theorem arithmetic_sub_self (value : Float64) (finite : value.exponent ≠ 2047) :
    arithmetic .sub value value = .ok (ofBits 0) := by
  have denominatorPositive : 0 < value.magnitudeRatio.2 := by
    by_cases subnormal : value.exponent = 0
    · simpa [magnitudeRatio, subnormal] using (Nat.pow_pos (n := 1074) (by decide : 0 < 2))
    · simp only [magnitudeRatio, beq_iff_eq, subnormal, ite_false]
      split
      · exact Nat.zero_lt_one
      · exact Nat.pow_pos (by decide : 0 < 2)
  have denominatorNonzero : value.magnitudeRatio.2 * value.magnitudeRatio.2 ≠ 0 :=
    Nat.ne_of_gt (Nat.mul_pos denominatorPositive denominatorPositive)
  cases signEquation : value.sign <;>
    simp [arithmetic, addSub, isNaN, isInf, finite, signEquation, fromRatio, denominatorNonzero]

def arithmeticIntFloat (operator : ArithmeticOp) (left : Int) (right : Float64) :
    Except ArithmeticError Float64 :=
  match fromInt left with
  | none => .error .conversionOverflow
  | some value => arithmetic operator value right

def arithmeticFloatInt (operator : ArithmeticOp) (left : Float64) (right : Int) :
    Except ArithmeticError Float64 :=
  match fromInt right with
  | none => .error .conversionOverflow
  | some value => arithmetic operator left value

inductive FloatDivisionError where
  | zeroDivision
  | conversionOverflow
  | nanPayload
deriving Repr, BEq, DecidableEq, Lean.ToExpr

def divideFinite (left right : Float64) : Except FloatDivisionError Float64 :=
  if right.isZero then .error .zeroDivision
  else if left.isNaN || right.isNaN || left.isInf && right.isInf then .error .nanPayload
  else
    let negative := left.sign != right.sign
    if left.isInf then
      .ok (ofBits ((if negative then 2 ^ 63 else 0) + 2047 * 2 ^ 52))
    else if right.isInf then .ok (ofBits (if negative then 2 ^ 63 else 0))
    else
      let (leftNumerator, leftDenominator) := left.magnitudeRatio
      let (rightNumerator, rightDenominator) := right.magnitudeRatio
      match fromRatio negative
          (leftNumerator * rightDenominator) (leftDenominator * rightNumerator) with
      | none => .error .zeroDivision
      | some value => .ok value

/-! CPython 3.9's pinned binary64 NaN propagation for true division. The
zero-denominator check remains first; otherwise the first NaN operand wins and
is quieted in place. The indeterminate `inf / inf` case uses the canonical
negative quiet NaN word observed on the pinned interpreter. -/
def divideFiniteWithNaN (left right : Float64) : Except FloatDivisionError Float64 :=
  if right.isZero then .error .zeroDivision
  else if left.isNaN then .ok (quietNaN left)
  else if right.isNaN then .ok (quietNaN right)
  else if left.isInf && right.isInf then .ok (ofBits 0xfff8000000000000)
  else divideFinite left right

def divideIntFloat (left : Int) (right : Float64) : Except FloatDivisionError Float64 :=
  match fromInt left with
  | none => .error .conversionOverflow
  | some value => divideFinite value right

def divideIntFloatWithNaN (left : Int) (right : Float64) : Except FloatDivisionError Float64 :=
  match fromInt left with
  | none => .error .conversionOverflow
  | some value => divideFiniteWithNaN value right

def divideFloatInt (left : Float64) (right : Int) : Except FloatDivisionError Float64 :=
  match fromInt right with
  | none => .error .conversionOverflow
  | some value => divideFinite left value

def divideFloatIntWithNaN (left : Float64) (right : Int) : Except FloatDivisionError Float64 :=
  match fromInt right with
  | none => .error .conversionOverflow
  | some value => divideFiniteWithNaN left value

private def divisionArithmetic (operator : ArithmeticOp) (left right : Float64) :
    Except FloatDivisionError Float64 :=
  match arithmetic operator left right with
  | .ok value => .ok value
  | .error .conversionOverflow => .error .conversionOverflow
  | .error .nanPayload => .error .nanPayload

private def floorIntegral (value : Float64) : Except FloatDivisionError Float64 :=
  if value.isInf || value.isZero then .ok value
  else
    match value.toRatio with
    | none => .error .nanPayload
    | some (numerator, denominator) =>
      match fromInt (Int.fdiv numerator denominator) with
      | none => .error .nanPayload
      | some result => .ok result

def floorRem (left right : Float64) : Except FloatDivisionError (Float64 × Float64) := do
  if right.isZero then throw .zeroDivision
  if left.isNaN || right.isNaN || left.isInf then throw .nanPayload
  let remainder ← if right.isInf then pure left else do
    let (leftNumerator, leftDenominator) := left.magnitudeRatio
    let (rightNumerator, rightDenominator) := right.magnitudeRatio
    match fromRatio left.sign
        ((leftNumerator * rightDenominator) % (rightNumerator * leftDenominator))
        (leftDenominator * rightDenominator) with
    | none => throw .nanPayload
    | some value => pure value
  let difference ← divisionArithmetic .sub left remainder
  let quotient ← divideFinite difference right
  let (quotient, remainder) ←
    if remainder.isZero then
      pure (quotient, ofBits (if right.sign then 2 ^ 63 else 0))
    else if remainder.sign != right.sign then do
      let correctedRemainder ← divisionArithmetic .add remainder right
      let correctedQuotient ← divisionArithmetic .sub quotient (ofBits 0x3ff0000000000000)
      pure (correctedQuotient, correctedRemainder)
    else pure (quotient, remainder)
  let floored ←
    if quotient.isZero then pure (ofBits (if left.sign != right.sign then 2 ^ 63 else 0))
    else if quotient.isInf then pure quotient
    else do
      let integral ← floorIntegral quotient
      let fraction ← divisionArithmetic .sub quotient integral
      if (ofBits 0x3fe0000000000000).lt fraction then
        divisionArithmetic .add integral (ofBits 0x3ff0000000000000)
      else pure integral
  return (floored, remainder)

/-! CPython 3.9's NaN behavior for floor division, remainder, and `divmod`.
The zero-denominator check precedes NaN classification; otherwise the first
NaN operand wins and is quieted in place. An infinite left operand with finite
or infinite non-NaN divisor uses the pinned canonical negative quiet NaN. -/
def floorRemWithNaN (left right : Float64) :
    Except FloatDivisionError (Float64 × Float64) :=
  if right.isZero then .error .zeroDivision
  else if left.isNaN then
    let value := quietNaN left
    .ok (value, value)
  else if right.isNaN then
    let value := quietNaN right
    .ok (value, value)
  else if left.isInf then
    let value := ofBits 0xfff8000000000000
    .ok (value, value)
  else floorRem left right

def floorRemIntFloat (left : Int) (right : Float64) :
    Except FloatDivisionError (Float64 × Float64) :=
  match fromInt left with
  | none => .error .conversionOverflow
  | some value => floorRem value right

def floorRemFloatInt (left : Float64) (right : Int) :
    Except FloatDivisionError (Float64 × Float64) :=
  match fromInt right with
  | none => .error .conversionOverflow
  | some value => floorRem left value

private def logarithm10 : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, value =>
    if value < 10 then 0 else 1 + logarithm10 fuel (value / 10)

private def scaleDecimal (numerator denominator : Nat) (power : Int) : Nat × Nat :=
  if power ≥ 0 then (numerator, denominator * 10 ^ power.toNat)
  else (numerator * 10 ^ (-power).toNat, denominator)

private def decimalExponent (numerator denominator : Nat) : Int :=
  let estimate := (logarithm10 400 numerator : Int) - (logarithm10 400 denominator : Int)
  let (scaledNumerator, scaledDenominator) := scaleDecimal numerator denominator estimate
  if scaledNumerator < scaledDenominator then estimate - 1 else estimate

private def midpoint (left right : Nat × Nat) : Nat × Nat :=
  (left.1 * right.2 + right.1 * left.2, 2 * left.2 * right.2)

private def decimalCoefficient (lower upper exact : Nat × Nat) (inclusive : Bool)
    (power : Int) : Option Nat :=
  let (lowerNumerator, lowerDenominator) := scaleDecimal lower.1 lower.2 power
  let (upperNumerator, upperDenominator) := scaleDecimal upper.1 upper.2 power
  let first := if inclusive then
    (lowerNumerator + lowerDenominator - 1) / lowerDenominator
    else lowerNumerator / lowerDenominator + 1
  let last := if inclusive then upperNumerator / upperDenominator
    else (upperNumerator - 1) / upperDenominator
  if first > last then none
  else
    let (exactNumerator, exactDenominator) := scaleDecimal exact.1 exact.2 power
    some (min last (max first (roundEven exactNumerator exactDenominator)))

private def shortestDecimal (lower upper exact : Nat × Nat) (inclusive : Bool)
    (decimalPower : Int) : Nat → Nat → Option (Nat × Int)
  | 0, _ => none
  | fuel + 1, digits =>
    let power := decimalPower - (digits : Int) + 1
    match decimalCoefficient lower upper exact inclusive power with
    | some coefficient => some (coefficient, power)
    | none => shortestDecimal lower upper exact inclusive decimalPower fuel (digits + 1)

private def stripZeros : Nat → Nat → Int → Nat × Int
  | 0, coefficient, power => (coefficient, power)
  | fuel + 1, coefficient, power =>
    if coefficient != 0 && coefficient % 10 == 0 then
      stripZeros fuel (coefficient / 10) (power + 1)
    else (coefficient, power)

private def zeros (count : Nat) : String := String.ofList (List.replicate count '0')

private def exponentText (power : Int) : String :=
  let magnitude := toString power.natAbs
  (if power < 0 then "-" else "+") ++
    (if power.natAbs < 10 then "0" else "") ++ magnitude

private def formatDecimal (coefficient : Nat) (power : Int) : String :=
  let text := toString coefficient
  let digits := logarithm10 400 coefficient + 1
  let decimalPoint := (digits : Int) + power
  let scientificPower := decimalPoint - 1
  if scientificPower < -4 || scientificPower ≥ 16 then
    let characters := text.toList
    String.ofList (characters.take 1) ++
      (if digits == 1 then "" else "." ++ String.ofList (characters.drop 1)) ++
      "e" ++ exponentText scientificPower
  else if power ≥ 0 then text ++ zeros power.toNat ++ ".0"
  else if decimalPoint ≤ 0 then "0." ++ zeros (-decimalPoint).toNat ++ text
  else
    let characters := text.toList
    String.ofList (characters.take decimalPoint.toNat) ++ "." ++
      String.ofList (characters.drop decimalPoint.toNat)

def repr (value : Float64) : Option String :=
  let signText := if value.sign then "-" else ""
  if value.isNaN then some "nan"
  else if value.isInf then some (signText ++ "inf")
  else if value.isZero then some (signText ++ "0.0")
  else
    let positive := value.abs
    let exact := positive.magnitudeRatio
    let previous := (ofBits (positive.bits.toNat - 1)).magnitudeRatio
    let following := (ofBits (positive.bits.toNat + 1)).magnitudeRatio
    let lower := midpoint previous exact
    let upper := midpoint exact following
    let inclusive := positive.bits.toNat % 2 == 0
    match shortestDecimal lower upper exact inclusive
        (decimalExponent exact.1 exact.2) 17 1 with
    | none => none
    | some (coefficient, power) =>
      let (coefficient, power) := stripZeros 17 coefficient power
      some (signText ++ formatDecimal coefficient power)

end Float64
end LeanModels.Python
