import LeanModels.Cpp.Types
import LeanModels.Cpp.Integral
import LeanModels.Cpp.TypeEvidence

namespace LeanModels.Cpp

inductive IntegralLogical where
  | conjunction
  | disjunction
  deriving Repr, BEq

def integralLogicalOfString : String → Option IntegralLogical
  | "&&" => some .conjunction
  | "||" => some .disjunction
  | _ => none

/-- The short-circuit result for a logical operation, when its left operand
    decides the result. A missing result means that the right operand must be
    evaluated. -/
def integralLogicalShortCircuit (operation : IntegralLogical) (left : IntegralValue) :
    Option IntegralValue :=
  match operation with
  | .conjunction => if left.value == 0 then some (integralBoolean false) else none
  | .disjunction => if left.value == 0 then none else some (integralBoolean true)

def integralBinaryOfString : String → Option IntegralBinary
  | "+" => some .add
  | "-" => some .subtract
  | "*" => some .multiply
  | "/" => some .divide
  | "%" => some .remainder
  | "<<" => some .shiftLeft
  | ">>" => some .shiftRight
  | "&" => some .bitAnd
  | "|" => some .bitOr
  | "^" => some .bitXor
  | "==" => some .equal
  | "!=" => some .notEqual
  | "<" => some .less
  | "<=" => some .lessEqual
  | ">" => some .greater
  | ">=" => some .greaterEqual
  | _ => none

def integralUnaryOfString : String → Option IntegralUnary
  | "+" => some .plus
  | "-" => some .negate
  | "~" => some .complement
  | "!" => some .logicalNot
  | _ => none

def integralCompoundBinaryOfString : String → Option IntegralBinary
  | "+=" => some .add
  | "-=" => some .subtract
  | "*=" => some .multiply
  | "/=" => some .divide
  | "%=" => some .remainder
  | "&=" => some .bitAnd
  | "|=" => some .bitOr
  | "^=" => some .bitXor
  | "<<=" => some .shiftLeft
  | ">>=" => some .shiftRight
  | _ => none

def integralIncrementBinaryOfString : String → Option IntegralBinary
  | "++" => some .add
  | "--" => some .subtract
  | _ => none

def integralTypeOfEvidence : CppTypeEvidence → Option CppIntType
  | .builtin type => some type
  | .qualified _ _ base => integralTypeOfEvidence base
  | _ => none

def integralFormatOfEvidence (profile : TargetProfile) (type : CppTypeEvidence) :
    Except TypeResolutionError IntegralFormat := do
  let some integer := integralTypeOfEvidence type
    | throw (.unsupportedType .int)
  profile.format integer

def mapIntegralResultValue (result : IntegralResult α) (map : α → β) : IntegralResult β :=
  match result with
  | .ok value => .ok (map value)
  | .invalid reason => .invalid reason
  | .undefined reason => .undefined reason
  | .unsupported reason => .unsupported reason

def bindIntegralResultValue (result : IntegralResult α)
    (continuation : α → IntegralResult β) : IntegralResult β :=
  match result with
  | .ok value => continuation value
  | .invalid reason => .invalid reason
  | .undefined reason => .undefined reason
  | .unsupported reason => .unsupported reason

def integralLiteralOfEvidence (profile : TargetProfile) (type : CppTypeEvidence)
    (value : Nat) : Except TypeResolutionError IntegralValue := do
  let format ← integralFormatOfEvidence profile type
  pure {format, value := Int.ofNat value}

/-- Execute an integral binary operation after C++'s promotions and usual
arithmetic conversions select one common destination format. The conversion
boundary is explicit so mixed signed/unsigned operands cannot silently reach
the same-format kernel with the wrong representation. -/
def integralBinaryUsual (profile : TargetProfile) (operation : IntegralBinary)
    (leftType rightType : CppIntType) (left right : IntegralValue) :
    IntegralResult IntegralValue :=
  if operation == .shiftLeft || operation == .shiftRight then
    match integralPromotion profile leftType, integralPromotion profile rightType with
    | .ok leftPromoted, .ok rightPromoted =>
        match profile.format leftPromoted, profile.format rightPromoted with
        | .ok leftFormat, .ok rightFormat =>
            bindIntegralResultValue (integralConvert leftFormat left) fun left =>
              bindIntegralResultValue (integralConvert rightFormat right) fun right =>
                integralBinary operation left right
        | _, _ => .unsupported .unresolvedArithmeticConversions
    | _, _ => .unsupported .unresolvedArithmeticConversions
  else
    match resolveArithmeticFormats profile leftType rightType with
    | .error _ => .unsupported .unresolvedArithmeticConversions
    | .ok (_, format) =>
        bindIntegralResultValue (integralConvert format left) fun left =>
          bindIntegralResultValue (integralConvert format right) fun right =>
            integralBinary operation left right

def integralSizeBytes (profile : TargetProfile) (type : CppIntType) :
    Except TypeResolutionError Nat :=
  match profile.format type with
  | .ok format => .ok ((format.width + 7) / 8)
  | .error reason => .error reason

def integralAlignBytes (profile : TargetProfile) (type : CppIntType) :
    Except TypeResolutionError Nat :=
  match integralSizeBytes profile type with
  | .ok bytes => .ok bytes
  | .error reason => .error reason

def integralSizeValueOfEvidence (profile : TargetProfile) (resultType operandType : CppTypeEvidence) :
    Except TypeResolutionError IntegralValue := do
  let format ← integralFormatOfEvidence profile resultType
  let some integer := integralTypeOfEvidence operandType
    | throw (.unsupportedType .int)
  let bytes ← integralSizeBytes profile integer
  pure {format, value := Int.ofNat bytes}

end LeanModels.Cpp
