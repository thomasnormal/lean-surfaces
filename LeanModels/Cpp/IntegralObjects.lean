import LeanModels.Cpp.ObjectModel

namespace LeanModels.Cpp

inductive IntegralObjectError where
  | invalidProfile
  | lifetime (reason : ObjectError)
  | unsupportedType (type : CppTypeEvidence)
  | invalidValue (reason : InvalidIntegral)
  | valueTypeMismatch
  | accessTypeMismatch
  | constWrite
  | referenceQualification
  | constDefaultInitialization
  | incoherentValues
  | missingValue (object : ObjectId)
  deriving Repr, BEq, Inhabited

structure IntegralObjectRef where
  object : ObjectId
  type : CppTypeEvidence
  deriving Repr, BEq, Inhabited

structure IntegralObjectStore where
  profile : TargetProfile
  objects : ObjectStore
  values : List (Option IntegralValue)
  deriving Repr, BEq, Inhabited

namespace IntegralObjectStore

private def integerKind : CppTypeEvidence → Option (CppIntType × Bool)
  | .builtin type => some (type, false)
  | .qualified isConst isVolatile base =>
      if isVolatile then none
      else (integerKind base).map fun (type, baseConst) => (type, isConst || baseConst)
  | _ => none

private def descriptor (type : CppTypeEvidence) :
    Except IntegralObjectError (CppIntType × Bool) :=
  match integerKind type with
  | some result => .ok result
  | none => .error (.unsupportedType type)

/-- Existing-object integral reference binding permits adding, never dropping,
const qualification. No value conversion or temporary is manufactured. -/
def validateReferenceTypes (source destination : CppTypeEvidence) :
    Except IntegralObjectError Unit := do
  let (sourceKind, sourceConst) ← descriptor source
  let (destinationKind, destinationConst) ← descriptor destination
  unless sourceKind == destinationKind do throw .accessTypeMismatch
  if sourceConst && !destinationConst then throw .referenceQualification

private def formatFor (profile : TargetProfile) (type : CppTypeEvidence) :
    Except IntegralObjectError IntegralFormat := do
  let (integer, _) ← descriptor type
  match profile.format integer with
  | .ok format => pure format
  | .error .invalidProfile => .error .invalidProfile
  | .error (.unsupportedType _) => .error (.unsupportedType type)

private def checkShape (store : IntegralObjectStore) : Except IntegralObjectError Unit := do
  unless store.profile.valid do throw .invalidProfile
  unless store.values.length == store.objects.objects.length do throw .incoherentValues

private def metadata (store : IntegralObjectStore) (object : ObjectId) :
    Except IntegralObjectError CppObject := do
  store.checkShape
  let some result := store.objects.object? object
    | throw (.lifetime (.missing object))
  let _ ← formatFor store.profile result.type
  pure result

private def checkValue (profile : TargetProfile) (type : CppTypeEvidence)
    (value : IntegralValue) : Except IntegralObjectError Unit := do
  let format ← formatFor profile type
  if let some reason := value.invalid? then throw (.invalidValue reason)
  unless value.format == format do throw .valueTypeMismatch

private def convertValue (profile : TargetProfile) (sourceType destinationType : CppTypeEvidence)
    (value : IntegralValue) : Except IntegralObjectError IntegralValue := do
  let _ ← checkValue profile sourceType value
  let destination ← formatFor profile destinationType
  match integralConvert destination value with
  | .ok converted => pure converted
  | .invalid reason => .error (.invalidValue reason)
  | .undefined _ => .error (.invalidValue .outOfRange)
  | .unsupported _ => .error .valueTypeMismatch

private def requireAlive (object : CppObject) : Except IntegralObjectError Unit :=
  match object.phase with
  | .storageOnly => .error (.lifetime .lifetimeNotStarted)
  | .aliveUninitialized | .aliveInitialized => .ok ()
  | .ended => .error (.lifetime .lifetimeEnded)
  | .released => .error (.lifetime .storageReleased)

private def validateAccess (store : IntegralObjectStore) (access : IntegralObjectRef) :
    Except IntegralObjectError CppObject := do
  let object ← store.metadata access.object
  let (actual, _) ← descriptor object.type
  let (requested, _) ← descriptor access.type
  unless actual == requested do throw .accessTypeMismatch
  requireAlive object
  pure object

def empty (profile : TargetProfile) : Except IntegralObjectError IntegralObjectStore :=
  if profile.valid then .ok {profile, objects := ObjectStore.empty, values := []}
  else .error .invalidProfile

def allocate (store : IntegralObjectStore) (duration : StorageDuration)
    (type : CppTypeEvidence) : Except IntegralObjectError (IntegralObjectStore × ObjectId) := do
  store.checkShape
  let _ ← formatFor store.profile type
  let (objects, object) := store.objects.allocate duration type
  pure ({store with objects, values := store.values ++ [none]}, object)

def initializeValue (store : IntegralObjectStore) (object : ObjectId) (value : IntegralValue) :
    Except IntegralObjectError IntegralObjectStore := do
  let entry ← store.metadata object
  checkValue store.profile entry.type value
  let started ← (store.objects.beginLifetime object).mapError IntegralObjectError.lifetime
  let objects ← (started.initializeObject object).mapError IntegralObjectError.lifetime
  pure {store with objects, values := store.values.modify object (fun _ => some value)}

def initializeConverted (store : IntegralObjectStore) (object : ObjectId)
    (sourceType : CppTypeEvidence) (value : IntegralValue) :
    Except IntegralObjectError IntegralObjectStore := do
  let entry ← store.metadata object
  let converted ← convertValue store.profile sourceType entry.type value
  initializeValue store object converted

/-- Rung-1 initialized automatic declaration: storage, lifetime start, source
    conversion, and value initialization are one typed declaration boundary. -/
def declareAutomaticInitialized (store : IntegralObjectStore)
    (type sourceType : CppTypeEvidence) (value : IntegralValue) :
    Except IntegralObjectError (IntegralObjectStore × ObjectId) := do
  let (reserved, object) ← store.allocate .automatic type
  let initialized ← reserved.initializeConverted object sourceType value
  pure (initialized, object)

def defaultInitialize (store : IntegralObjectStore) (object : ObjectId) :
    Except IntegralObjectError IntegralObjectStore := do
  let entry ← store.metadata object
  let (_, isConst) ← descriptor entry.type
  if isConst then throw .constDefaultInitialization
  let objects ← (store.objects.beginLifetime object).mapError IntegralObjectError.lifetime
  pure {store with objects, values := store.values.modify object (fun _ => none)}

def borrow (store : IntegralObjectStore) (object : ObjectId) (readOnly : Bool := false) :
    Except IntegralObjectError IntegralObjectRef := do
  let entry ← store.metadata object
  requireAlive entry
  pure {object, type := if readOnly then .qualified true false entry.type else entry.type}

/-- Bind another view without reading or allocating the live referent. -/
def bindReference (store : IntegralObjectStore) (source : IntegralObjectRef)
    (referent : CppTypeEvidence) : Except IntegralObjectError IntegralObjectRef := do
  let entry ← store.validateAccess source
  validateReferenceTypes source.type referent
  validateReferenceTypes entry.type referent
  pure {object := source.object, type := referent}

def read (store : IntegralObjectStore) (access : IntegralObjectRef) :
    Except IntegralObjectError IntegralValue := do
  let entry ← store.validateAccess access
  let _ ← (store.objects.readType access.object).mapError IntegralObjectError.lifetime
  let some (some value) := store.values[access.object]?
    | throw (.missingValue access.object)
  checkValue store.profile entry.type value
  pure value

def assign (store : IntegralObjectStore) (access : IntegralObjectRef) (value : IntegralValue) :
    Except IntegralObjectError IntegralObjectStore := do
  let entry ← store.validateAccess access
  let (_, objectConst) ← descriptor entry.type
  let (_, accessConst) ← descriptor access.type
  if objectConst || accessConst then throw .constWrite
  checkValue store.profile entry.type value
  let objects ← match entry.phase with
    | .aliveUninitialized =>
        (store.objects.initializeObject access.object).mapError IntegralObjectError.lifetime
    | _ => pure store.objects
  pure {store with objects, values := store.values.modify access.object (fun _ => some value)}

def assignConverted (store : IntegralObjectStore) (access : IntegralObjectRef)
    (sourceType : CppTypeEvidence) (value : IntegralValue) :
    Except IntegralObjectError IntegralObjectStore := do
  let entry ← store.validateAccess access
  let (_, objectConst) ← descriptor entry.type
  let (_, accessConst) ← descriptor access.type
  if objectConst || accessConst then throw .constWrite
  let converted ← convertValue store.profile sourceType entry.type value
  let objects ← match entry.phase with
    | .aliveUninitialized =>
        (store.objects.initializeObject access.object).mapError IntegralObjectError.lifetime
    | _ => pure store.objects
  pure {store with objects, values := store.values.modify access.object (fun _ => some converted)}

def endLifetime (store : IntegralObjectStore) (object : ObjectId) :
    Except IntegralObjectError IntegralObjectStore := do
  let _ ← store.metadata object
  let objects ← (store.objects.endLifetime object).mapError IntegralObjectError.lifetime
  pure {store with objects, values := store.values.modify object (fun _ => none)}

def releaseStorage (store : IntegralObjectStore) (object : ObjectId) :
    Except IntegralObjectError IntegralObjectStore := do
  let _ ← store.metadata object
  let objects ← (store.objects.releaseStorage object).mapError IntegralObjectError.lifetime
  pure {store with objects, values := store.values.modify object (fun _ => none)}

end IntegralObjectStore

end LeanModels.Cpp
