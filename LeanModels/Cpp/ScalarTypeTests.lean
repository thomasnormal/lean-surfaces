import LeanModels.Cpp.ScalarTypes

namespace LeanModels.Cpp.ScalarTypeTests

def integer : CppQualifiedScalar := .unqualified (.integral .int)
def floating : CppQualifiedScalar := .unqualified (.floating .double)

#guard CppScalarType.void.isObject == false
#guard (CppScalarType.integral .int).isObject
#guard (CppScalarType.integral .int).isIntegral
#guard (CppScalarType.character .char16).isIntegral
#guard (CppScalarType.floating .double).isFloating
#guard (CppScalarType.floating .double).isArithmetic
#guard CppScalarType.void.isArithmetic == false

#guard (integer.addConst.addVolatile).cv == {isConst := true, isVolatile := true}
#guard integer.addConst.removeCv == integer
#guard integer.addConst.sameUnqualified integer.addVolatile
#guard integer.sameUnqualified floating == false
#guard integer.addConst.isIntegral
#guard floating.addVolatile.isFloating

#guard ScalarProfile.lp64.valid
#guard scalarWidthBits .lp64 (.integral .int) matches .ok 32
#guard scalarWidthBits .lp64 (.integral .longLong) matches .ok 64
#guard scalarWidthBits .lp64 (.character .char32) matches .ok 32
#guard scalarWidthBits .lp64 (.floating .double) matches .ok 64
#guard qualifiedScalarWidthBits .lp64 integer.addConst matches .ok 32
#guard scalarWidthBits .lp64 .void matches .error .voidType

def narrowProfile : ScalarProfile := {ScalarProfile.lp64 with
  integers := {TargetProfile.lp64 with intWidth := 8}}

#guard narrowProfile.valid == false
#guard scalarWidthBits narrowProfile (.integral .int) matches .error .invalidProfile
#guard CppIntType.long != CppIntType.longLong

end LeanModels.Cpp.ScalarTypeTests
