import LeanModels.Cpp.CompositeTypes

namespace LeanModels.Cpp.CompositeTypeTests

def integer : CppType := .scalar (.integral .int)
def constInteger : CppType := integer.addConst
def pointer : CppType := .pointer constInteger
def boundedArray : CppType := .array integer (some 4)
def incompleteArray : CppType := .array integer none

#guard integer.isObject
#guard integer.isComplete
#guard constInteger.isComplete
#guard pointer.isObject
#guard pointer.isComplete
#guard pointer.pointerDepth == 1
#guard (CppType.pointer (CppType.pointer integer)).pointerDepth == 2
#guard boundedArray.isObject
#guard boundedArray.isComplete
#guard incompleteArray.isComplete == false
#guard boundedArray.topArrayBound? == some 4
#guard pointer.topArrayBound?.isNone

#guard validateCppType integer matches .ok ()
#guard validateCppType pointer matches .ok ()
#guard validateCppType boundedArray matches .ok ()
#guard validateCppType incompleteArray matches .ok ()
#guard validateCppType (.array (.scalar .void) (some 1)) matches .error .arrayOfVoid
#guard validateCppType (.array integer (some 0)) matches .error .zeroBound
#guard validateCppType (.qualified false false integer) matches .error .emptyQualification

#guard constInteger.sameIgnoringTopCv integer
#guard constInteger.removeTopCv == integer
#guard integer.addVolatile.sameIgnoringTopCv constInteger
#guard integer.isVoid == false
#guard (CppType.scalar .void).isVoid
#guard (CppType.scalar .void).isObject == false
#guard (CppType.pointer (CppType.scalar .void)).isObject

end LeanModels.Cpp.CompositeTypeTests
