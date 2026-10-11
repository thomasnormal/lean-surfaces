import LeanModels.Cpp.CompositeTypes

namespace LeanModels.Cpp

inductive CppValueCategory where
  | lvalue
  | xvalue
  | prvalue
  deriving Repr, BEq, Inhabited

inductive CppReferenceKind where
  | lvalue
  | rvalue
  deriving Repr, BEq, Inhabited

structure CppReferenceType where
  kind : CppReferenceKind
  referent : CppType
  deriving Repr, BEq, Inhabited

namespace CppReferenceType

def lvalue (referent : CppType) : CppReferenceType :=
  {kind := .lvalue, referent}

def rvalue (referent : CppType) : CppReferenceType :=
  {kind := .rvalue, referent}

end CppReferenceType

structure ReferenceExpression where
  type : CppType
  category : CppValueCategory
  deriving Repr, BEq, Inhabited

inductive ReferenceBindingError where
  | invalidReferenceType
  | categoryMismatch
  | typeMismatch
  deriving Repr, BEq, Inhabited

def validateReferenceType (reference : CppReferenceType) :
    Except ReferenceBindingError Unit := do
  if reference.referent.isVoid then .error .invalidReferenceType
  else match validateCppType reference.referent with
    | .ok () => .ok ()
    | .error _ => .error .invalidReferenceType

def bindReference (reference : CppReferenceType)
    (expression : ReferenceExpression) : Except ReferenceBindingError Unit := do
  validateReferenceType reference
  if reference.referent != expression.type then .error .typeMismatch
  else match reference.kind, expression.category with
    | .lvalue, .lvalue => .ok ()
    | .rvalue, .xvalue | .rvalue, .prvalue => .ok ()
    | _, _ => .error .categoryMismatch

end LeanModels.Cpp
