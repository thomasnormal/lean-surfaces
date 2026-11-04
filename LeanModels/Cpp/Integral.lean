import Init.Data.Int.DivMod.Basic
import Init.Data.Int.Bitwise.Basic

namespace LeanModels.Cpp

inductive IntegralFormat where
  | boolean
  | signed (width : Nat)
  | unsigned (width : Nat)
  deriving Repr, BEq, Inhabited

def IntegralFormat.width : IntegralFormat → Nat
  | .boolean => 1
  | .signed width | .unsigned width => width

def IntegralFormat.minimum : IntegralFormat → Int
  | .signed width => -(2 ^ (width - 1) : Int)
  | _ => 0

def IntegralFormat.maximum : IntegralFormat → Int
  | .boolean => 1
  | .signed width => (2 ^ (width - 1) : Int) - 1
  | .unsigned width => (2 ^ width : Int) - 1

def IntegralFormat.contains (format : IntegralFormat) (value : Int) : Bool :=
  format.minimum ≤ value && value ≤ format.maximum

def IntegralFormat.wrap (format : IntegralFormat) (value : Int) : Int :=
  match format with
  | .boolean => if value == 0 then 0 else 1
  | .unsigned width => value % (2 ^ width : Int)
  | .signed width =>
      let residue := value % (2 ^ width : Int)
      if residue ≥ (2 ^ (width - 1) : Int) then residue - (2 ^ width : Int) else residue

structure IntegralValue where
  format : IntegralFormat
  value : Int
  deriving Repr, BEq, Inhabited

inductive InvalidIntegral where
  | zeroWidth
  | outOfRange
  deriving Repr, BEq, Inhabited

inductive IntegralUB where
  | signedOverflow
  | divisionByZero
  | divisionOverflow
  | negativeShift
  | excessiveShift
  deriving Repr, BEq, Inhabited

inductive IntegralUnsupported where
  | unpromotedBoolean
  | unresolvedArithmeticConversions
  deriving Repr, BEq, Inhabited

inductive IntegralResult (α : Type) where
  | ok (value : α)
  | invalid (reason : InvalidIntegral)
  | undefined (reason : IntegralUB)
  | unsupported (reason : IntegralUnsupported)
  deriving Repr, BEq, Inhabited

def IntegralValue.invalid? (value : IntegralValue) : Option InvalidIntegral :=
  if value.format.width == 0 then some .zeroWidth
  else if !value.format.contains value.value then some .outOfRange
  else none

def integralConvert (destination : IntegralFormat) (source : IntegralValue) :
    IntegralResult IntegralValue :=
  match source.invalid? with
  | some reason => .invalid reason
  | none =>
      if destination.width == 0 then .invalid .zeroWidth
      else .ok ⟨destination, destination.wrap source.value⟩

private def integralArithmetic (format : IntegralFormat) (value : Int) : IntegralResult IntegralValue :=
  match format with
  | .boolean => .unsupported .unpromotedBoolean
  | .signed _ =>
      if format.contains value then .ok ⟨format, value⟩ else .undefined .signedOverflow
  | .unsigned _ => .ok ⟨format, format.wrap value⟩

def integralBoolean (value : Bool) : IntegralValue :=
  ⟨.boolean, if value then 1 else 0⟩

inductive IntegralUnary where
  | plus | negate | complement | logicalNot
  deriving Repr, BEq, Inhabited

def integralUnary (operation : IntegralUnary) (operand : IntegralValue) :
    IntegralResult IntegralValue :=
  match operand.invalid? with
  | some reason => .invalid reason
  | none =>
      match operation with
      | .logicalNot => .ok (integralBoolean (operand.value == 0))
      | _ =>
          if operand.format == .boolean then .unsupported .unpromotedBoolean
          else match operation with
            | .plus => .ok operand
            | .negate => integralArithmetic operand.format (-operand.value)
            | .complement => .ok ⟨operand.format, operand.format.wrap (-operand.value - 1)⟩
            | .logicalNot => .ok (integralBoolean (operand.value == 0))

inductive IntegralBinary where
  | add | subtract | multiply | divide | remainder
  | shiftLeft | shiftRight | bitAnd | bitOr | bitXor
  | equal | notEqual | less | lessEqual | greater | greaterEqual
  deriving Repr, BEq, Inhabited

private def integralShift (operation : IntegralBinary) (left right : IntegralValue) :
    IntegralResult IntegralValue :=
  if right.value < 0 then .undefined .negativeShift
  else if right.value ≥ (left.format.width : Int) then .undefined .excessiveShift
  else if operation == .shiftLeft then
    .ok ⟨left.format, left.format.wrap (left.value * (2 ^ right.value.toNat : Int))⟩
  else .ok ⟨left.format, left.value >>> right.value.toNat⟩

private def integralDivision (operation : IntegralBinary) (left right : IntegralValue) :
    IntegralResult IntegralValue :=
  if right.value == 0 then .undefined .divisionByZero
  else
    let quotient := left.value.tdiv right.value
    if !left.format.contains quotient then .undefined .divisionOverflow
    else .ok ⟨left.format,
      if operation == .divide then quotient else left.value.tmod right.value⟩

private def integralBits (operation : IntegralBinary) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | remaining + 1, left, right =>
      let leftBit := left % 2 == 1
      let rightBit := right % 2 == 1
      let bit := match operation with
        | .bitAnd => leftBit && rightBit
        | .bitOr => leftBit || rightBit
        | _ => leftBit != rightBit
      2 * integralBits operation remaining (left / 2) (right / 2) + if bit then 1 else 0

private def integralBinaryResolved (operation : IntegralBinary) (left right : IntegralValue) :
    IntegralResult IntegralValue :=
  match operation with
  | .add => integralArithmetic left.format (left.value + right.value)
  | .subtract => integralArithmetic left.format (left.value - right.value)
  | .multiply => integralArithmetic left.format (left.value * right.value)
  | .divide | .remainder => integralDivision operation left right
  | .shiftLeft | .shiftRight => integralShift operation left right
  | .bitAnd | .bitOr | .bitXor =>
      let leftBits := (left.value % (2 ^ left.format.width : Int)).toNat
      let rightBits := (right.value % (2 ^ right.format.width : Int)).toNat
      let bits := integralBits operation left.format.width leftBits rightBits
      .ok ⟨left.format, left.format.wrap bits⟩
  | .equal => .ok (integralBoolean (left.value == right.value))
  | .notEqual => .ok (integralBoolean (left.value != right.value))
  | .less => .ok (integralBoolean (left.value < right.value))
  | .lessEqual => .ok (integralBoolean (left.value ≤ right.value))
  | .greater => .ok (integralBoolean (left.value > right.value))
  | .greaterEqual => .ok (integralBoolean (left.value ≥ right.value))

def integralBinary (operation : IntegralBinary) (left right : IntegralValue) :
    IntegralResult IntegralValue :=
  match left.invalid?, right.invalid? with
  | some reason, _ | _, some reason => .invalid reason
  | none, none =>
      if left.format == .boolean || right.format == .boolean then
        .unsupported .unpromotedBoolean
      else if operation == .shiftLeft || operation == .shiftRight then
        integralBinaryResolved operation left right
      else if left.format != right.format then .unsupported .unresolvedArithmeticConversions
      else integralBinaryResolved operation left right

end LeanModels.Cpp
