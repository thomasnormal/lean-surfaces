import LeanModels.Cpp.ReferenceTypes

namespace LeanModels.Cpp.ReferenceTypeTests

def integer : CppType := .scalar (.integral .int)
def constInteger : CppType := integer.addConst
def lvalueInteger : CppReferenceType := .lvalue integer
def rvalueInteger : CppReferenceType := .rvalue integer

def lvalueExpression : ReferenceExpression := {type := integer, category := .lvalue}
def xvalueExpression : ReferenceExpression := {type := integer, category := .xvalue}
def prvalueExpression : ReferenceExpression := {type := integer, category := .prvalue}

#guard validateReferenceType lvalueInteger matches .ok ()
#guard validateReferenceType rvalueInteger matches .ok ()
#guard validateReferenceType (.lvalue (.scalar .void)) matches .error .invalidReferenceType
#guard validateReferenceType (.lvalue (.array integer none)) matches .ok ()

#guard bindReference lvalueInteger lvalueExpression matches .ok ()
#guard bindReference rvalueInteger xvalueExpression matches .ok ()
#guard bindReference rvalueInteger prvalueExpression matches .ok ()
#guard bindReference lvalueInteger prvalueExpression matches .error .categoryMismatch
#guard bindReference rvalueInteger lvalueExpression matches .error .categoryMismatch
#guard bindReference lvalueInteger {type := constInteger, category := .lvalue} matches
  .error .typeMismatch
#guard bindReference (.lvalue constInteger)
    {type := constInteger, category := .lvalue} matches .ok ()

end LeanModels.Cpp.ReferenceTypeTests
