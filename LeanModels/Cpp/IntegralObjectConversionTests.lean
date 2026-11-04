import LeanModels.Cpp.IntegralObjects

namespace LeanModels.Cpp.IntegralObjectConversionTests

open LeanModels.Cpp

private def signed (width : Nat) (value : Int) : IntegralValue := ⟨.signed width, value⟩
private def unsigned (width : Nat) (value : Int) : IntegralValue := ⟨.unsigned width, value⟩
private def intType : CppTypeEvidence := .builtin .int
private def shortType : CppTypeEvidence := .builtin .short
private def unsignedType : CppTypeEvidence := .builtin .unsignedInt
private def boolType : CppTypeEvidence := .builtin .boolean

private def allocated (type : CppTypeEvidence := intType) :
    Except IntegralObjectError (IntegralObjectStore × ObjectId) := do
  let store ← IntegralObjectStore.empty .lp64
  store.allocate .automatic type

private def valueIs (expected : IntegralValue)
    (result : Except IntegralObjectError IntegralValue) : Bool :=
  match result with
  | .ok value => value == expected
  | .error _ => false

#guard valueIs (signed 16 (-25536)) (do
  let (store, object) ← allocated shortType
  let store ← store.initializeConverted object intType (signed 32 40000)
  let access ← store.borrow object
  store.read access)

#guard valueIs (signed 16 25536) (do
  let (store, object) ← allocated shortType
  let store ← store.defaultInitialize object
  let access ← store.borrow object
  let store ← store.assignConverted access intType (signed 32 (-40000))
  store.read access)

#guard valueIs ⟨.boolean, 1⟩ (do
  let (store, object) ← allocated boolType
  let store ← store.initializeConverted object intType (signed 32 (-7))
  let access ← store.borrow object
  store.read access)

#guard valueIs (unsigned 32 4294967295) (do
  let (store, object) ← allocated unsignedType
  let store ← store.initializeConverted object intType (signed 32 (-1))
  let access ← store.borrow object
  store.read access)

#guard (do
  let (store, object) ← allocated shortType
  store.initializeConverted object intType (signed 16 7) :
    Except IntegralObjectError IntegralObjectStore) matches .error .valueTypeMismatch

#guard (do
  let (store, object) ← allocated shortType
  store.initializeConverted object (.pointer intType) (signed 32 7) :
    Except IntegralObjectError IntegralObjectStore) matches .error (.unsupportedType _)

#guard (do
  let (store, object) ← allocated shortType
  let store ← store.initializeConverted object intType (signed 32 7)
  let access ← store.borrow object true
  store.assignConverted access intType (signed 32 8) :
    Except IntegralObjectError IntegralObjectStore) matches .error .constWrite

#guard (do
  let (store, object) ← allocated shortType
  let store ← store.defaultInitialize object
  let access ← store.borrow object
  let store ← store.assignConverted access intType (signed 32 7)
  store.assignConverted access (.pointer intType) (signed 32 7) :
    Except IntegralObjectError IntegralObjectStore) matches .error (.unsupportedType _)

#guard (do
  let (store, object) ← allocated shortType
  store.initializeConverted object intType ⟨.signed 32, 2147483648⟩ :
    Except IntegralObjectError IntegralObjectStore) matches .error (.invalidValue .outOfRange)

end LeanModels.Cpp.IntegralObjectConversionTests
