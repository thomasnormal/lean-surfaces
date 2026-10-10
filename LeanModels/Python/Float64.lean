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
  ⟨value.bits ^^^ UInt64.ofNat (2 ^ 63)⟩

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

inductive FloatDivisionError where
  | zeroDivision
  | conversionOverflow
  | nonFinite
deriving Repr, BEq, DecidableEq, Lean.ToExpr

def divideFinite (left right : Float64) : Except FloatDivisionError Float64 :=
  if right.isZero then .error .zeroDivision
  else if left.exponent == 2047 || right.exponent == 2047 then .error .nonFinite
  else
    let (leftNumerator, leftDenominator) := left.magnitudeRatio
    let (rightNumerator, rightDenominator) := right.magnitudeRatio
    match fromRatio (left.sign != right.sign)
        (leftNumerator * rightDenominator) (leftDenominator * rightNumerator) with
    | none => .error .zeroDivision
    | some value => .ok value

def divideIntFloat (left : Int) (right : Float64) : Except FloatDivisionError Float64 :=
  match fromInt left with
  | none => .error .conversionOverflow
  | some value => divideFinite value right

def divideFloatInt (left : Float64) (right : Int) : Except FloatDivisionError Float64 :=
  match fromInt right with
  | none => .error .conversionOverflow
  | some value => divideFinite left value

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
