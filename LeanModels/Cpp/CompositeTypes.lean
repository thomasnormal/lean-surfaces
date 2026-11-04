import LeanModels.Cpp.ScalarTypes

namespace LeanModels.Cpp

inductive CppType where
  | scalar (type : CppScalarType)
  | pointer (pointee : CppType)
  | array (element : CppType) (bound : Option Nat)
  | qualified (isConst isVolatile : Bool) (base : CppType)
  deriving Repr, BEq, Inhabited

namespace CppType

def unqualified : CppType → CppType
  | .qualified _ _ base => unqualified base
  | type => type

def isVoid (type : CppType) : Bool :=
  match type.unqualified with
  | .scalar .void => true
  | _ => false

def isObject : CppType → Bool
  | CppType.scalar baseType => baseType.isObject
  | CppType.pointer _ | CppType.array _ _ => true
  | CppType.qualified _ _ base => base.isObject

def isComplete : CppType → Bool
  | CppType.scalar baseType => baseType != .void
  | CppType.pointer _ => true
  | CppType.array element (some bound) => bound > 0 && element.isComplete
  | CppType.array _ none => false
  | CppType.qualified _ _ base => base.isComplete

def pointerDepth : CppType → Nat
  | .pointer pointee => pointee.pointerDepth + 1
  | .qualified _ _ base => base.pointerDepth
  | _ => 0

def topArrayBound? : CppType → Option Nat
  | .array _ bound => bound
  | .qualified _ _ base => base.topArrayBound?
  | _ => none

def addConst (type : CppType) : CppType :=
  .qualified true false type

def addVolatile (type : CppType) : CppType :=
  .qualified false true type

def removeTopCv : CppType → CppType
  | .qualified _ _ base => base
  | type => type

def sameIgnoringTopCv (left right : CppType) : Bool :=
  left.removeTopCv == right.removeTopCv

end CppType

inductive CppTypeError where
  | emptyQualification
  | arrayOfVoid
  | zeroBound
  deriving Repr, BEq, Inhabited

def validateCppType : CppType → Except CppTypeError Unit
  | .scalar _ => .ok ()
  | .pointer pointee => validateCppType pointee
  | .array element bound => do
      validateCppType element
      if element.isVoid then .error .arrayOfVoid
      else match bound with
        | some 0 => .error .zeroBound
        | _ => .ok ()
  | .qualified isConst isVolatile base =>
      if !isConst && !isVolatile then .error .emptyQualification
      else validateCppType base

end LeanModels.Cpp
