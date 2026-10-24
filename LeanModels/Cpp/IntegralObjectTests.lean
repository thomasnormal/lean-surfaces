import LeanModels.Cpp.IntegralObjects

namespace LeanModels.Cpp.IntegralObjectTests

open LeanModels.Cpp

private def signed (value : Int) : IntegralValue := ⟨.signed 32, value⟩

private def matchesValue (expected : IntegralValue)
    (result : Except IntegralObjectError IntegralValue) : Bool :=
  match result with
  | .ok value => value == expected
  | .error _ => false

private def allocated (type : CppTypeEvidence := .builtin .int)
    (duration : StorageDuration := .automatic) :
    Except IntegralObjectError (IntegralObjectStore × ObjectId) := do
  let store ← IntegralObjectStore.empty .lp64
  store.allocate duration type

private def initialized (type : CppTypeEvidence := .builtin .int)
    (duration : StorageDuration := .automatic) :
    Except IntegralObjectError (IntegralObjectStore × ObjectId) := do
  let (store, object) ← allocated type duration
  let store ← store.initializeValue object (signed 7)
  pure (store, object)

private def aliasTrace : Except IntegralObjectError (List IntegralValue) := do
  let (store, first) ← initialized
  let (store, second) ← store.allocate .automatic (.builtin .int)
  let store ← store.initializeValue second (signed 7)
  let access ← store.borrow first
  let alias ← store.borrow first
  let distinct ← store.borrow second
  let before ← store.read access
  let store ← store.assign alias (signed (-5))
  let after ← store.read access
  let untouched ← store.read distinct
  pure [before, after, untouched]

#guard match aliasTrace with
  | .ok values => values == [signed 7, signed (-5), signed 7]
  | .error _ => false

#guard (do
  let (store, object) ← allocated
  let store ← store.defaultInitialize object
  let access ← store.borrow object
  store.read access : Except IntegralObjectError IntegralValue) matches
    .error (.lifetime .notInitialized)

#guard matchesValue (signed 11) (do
  let (store, object) ← allocated
  let store ← store.defaultInitialize object
  let access ← store.borrow object
  let store ← store.assign access (signed 11)
  store.read access : Except IntegralObjectError IntegralValue)

#guard (do
  let (store, object) ← allocated
  store.borrow object : Except IntegralObjectError IntegralObjectRef) matches
    .error (.lifetime .lifetimeNotStarted)

#guard (do
  let (store, object) ← initialized
  store.initializeValue object (signed 3) : Except IntegralObjectError IntegralObjectStore) matches
    .error (.lifetime .alreadyStarted)

#guard (do
  let (store, object) ← initialized
  let access ← store.borrow object true
  store.assign access (signed 3) : Except IntegralObjectError IntegralObjectStore) matches
    .error .constWrite

#guard matchesValue (signed 7) (do
  let (store, object) ← initialized
  let access ← store.borrow object true
  store.read access : Except IntegralObjectError IntegralValue)

#guard matchesValue (signed 7) (do
  let (store, object) ← initialized (.qualified true false (.builtin .int))
  let access ← store.borrow object
  store.read access : Except IntegralObjectError IntegralValue)

#guard (do
  let (store, object) ← initialized (.qualified true false (.builtin .int))
  store.assign {object, type := .builtin .int} (signed 3) :
    Except IntegralObjectError IntegralObjectStore) matches .error .constWrite

#guard (do
  let (store, object) ← allocated (.qualified true false (.builtin .int))
  store.defaultInitialize object : Except IntegralObjectError IntegralObjectStore) matches
    .error .constDefaultInitialization

#guard (do
  let (store, object) ← initialized
  let access ← store.borrow object
  let store ← store.endLifetime object
  store.read access : Except IntegralObjectError IntegralValue) matches
    .error (.lifetime .lifetimeEnded)

#guard (do
  let (store, object) ← initialized
  let access ← store.borrow object
  let store ← store.endLifetime object
  store.assign access (signed 3) : Except IntegralObjectError IntegralObjectStore) matches
    .error (.lifetime .lifetimeEnded)

#guard (do
  let (store, object) ← initialized (.builtin .int) .dynamic
  let access ← store.borrow object
  let store ← store.endLifetime object
  let store ← store.releaseStorage object
  store.read access : Except IntegralObjectError IntegralValue) matches
    .error (.lifetime .storageReleased)

#guard (do
  let (store, object) ← initialized (.builtin .int) .dynamic
  let stale ← store.borrow object
  let store ← store.endLifetime object
  let store ← store.releaseStorage object
  let (store, fresh) ← store.allocate .dynamic (.builtin .int)
  let store ← store.initializeValue fresh (signed 19)
  store.read stale : Except IntegralObjectError IntegralValue) matches
    .error (.lifetime .storageReleased)

#guard (do
  let (store, object) ← initialized (.builtin .int) .dynamic
  store.releaseStorage object : Except IntegralObjectError IntegralObjectStore) matches
    .error (.lifetime .dynamicStorageLive)

#guard (do
  let (store, object) ← initialized
  let store ← store.endLifetime object
  store.releaseStorage object : Except IntegralObjectError IntegralObjectStore) matches
    .error (.lifetime .notDynamicStorage)

#guard (do
  let (store, object) ← allocated
  store.initializeValue object ⟨.signed 32, 2147483648⟩ :
    Except IntegralObjectError IntegralObjectStore) matches .error (.invalidValue .outOfRange)

#guard (do
  let (store, object) ← initialized
  let access ← store.borrow object
  store.assign access ⟨.signed 32, 2147483648⟩ :
    Except IntegralObjectError IntegralObjectStore) matches .error (.invalidValue .outOfRange)

#guard (do
  let (store, object) ← allocated
  store.initializeValue object ⟨.unsigned 32, 7⟩ :
    Except IntegralObjectError IntegralObjectStore) matches .error .valueTypeMismatch

#guard (do
  let (store, object) ← initialized
  store.read {object, type := .builtin .unsignedInt} :
    Except IntegralObjectError IntegralValue) matches .error .accessTypeMismatch

#guard (do
  let (store, object) ← allocated (.builtin .long)
  let store ← store.initializeValue object ⟨.signed 64, 7⟩
  store.read {object, type := .builtin .longLong} :
    Except IntegralObjectError IntegralValue) matches .error .accessTypeMismatch

#guard (allocated (.qualified false true (.builtin .int))) matches .error (.unsupportedType _)
#guard (allocated (.pointer (.builtin .int))) matches .error (.unsupportedType _)
#guard (allocated (.record {value := "record"})) matches .error (.unsupportedType _)
#guard (IntegralObjectStore.empty {TargetProfile.lp64 with intWidth := 8}) matches
  .error .invalidProfile

#guard (do
  let store ← IntegralObjectStore.empty .lp64
  let incoherent := {store with values := [some (signed 7)]}
  incoherent.allocate .automatic (.builtin .int) :
    Except IntegralObjectError (IntegralObjectStore × ObjectId)) matches .error .incoherentValues

#guard (do
  let (store, object) ← initialized
  let access ← store.borrow object
  let missing := {store with values := [none]}
  missing.read access : Except IntegralObjectError IntegralValue) matches .error (.missingValue _)

#guard (do
  let (store, object) ← initialized
  let access ← store.borrow object
  let invalid := {store with values := [some ⟨.signed 32, 2147483648⟩]}
  invalid.read access : Except IntegralObjectError IntegralValue) matches
    .error (.invalidValue .outOfRange)

#guard (do
  let (store, object) ← initialized
  let access ← store.borrow object
  let store ← store.endLifetime object
  let store ← store.reuseEnded object (.builtin .int)
  let store ← store.initializeConverted object (.builtin .short) ⟨.signed 16, 19⟩
  store.read access : Except IntegralObjectError IntegralValue) matches .ok ⟨.signed 32, 19⟩

#guard (do
  let (store, object) ← initialized
  store.reuseEnded object (.builtin .int) : Except IntegralObjectError IntegralObjectStore)
    matches .error (.lifetime .lifetimeNotEnded)

end LeanModels.Cpp.IntegralObjectTests
