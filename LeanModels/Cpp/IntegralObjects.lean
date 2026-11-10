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

structure StaticObjectBinding where
  declaration : FrontendHandle
  object : ObjectId
  type : CppTypeEvidence
  deriving Repr, BEq, Inhabited

structure ThreadObjectBinding where
  declaration : FrontendHandle
  object : ObjectId
  type : CppTypeEvidence
  deriving Repr, BEq, Inhabited

structure IntegralObjectStore where
  profile : TargetProfile
  objects : ObjectStore
  values : List (Option IntegralValue)
  staticBindings : List StaticObjectBinding := []
  threadBindings : List ThreadObjectBinding := []
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
  if profile.valid then
    .ok {profile, objects := ObjectStore.empty, values := [], staticBindings := [], threadBindings := []}
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

/-- Materialize an already-evaluated integral prvalue as a temporary object.
    The returned identity remains temporary until a caller extends it. -/
def materializeTemporary (store : IntegralObjectStore)
    (type sourceType : CppTypeEvidence) (value : IntegralValue) :
    Except IntegralObjectError (IntegralObjectStore × ObjectId) := do
  let (reserved, object) ← store.allocate .temporary type
  let initialized ← reserved.initializeConverted object sourceType value
  pure (initialized, object)

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

/-- Zero-initialize an integral object with the destination type's own format.
    Unlike vacuous default-initialization, this publishes a defined zero value
    and is permitted for const-qualified objects. -/
def zeroInitialize (store : IntegralObjectStore) (object : ObjectId) :
    Except IntegralObjectError IntegralObjectStore := do
  let entry ← store.metadata object
  let format ← formatFor store.profile entry.type
  store.initializeValue object ⟨format, 0⟩

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

/-- Extend a live temporary to the surrounding scope without allocating or
    changing its stored value. -/
def extendTemporary (store : IntegralObjectStore) (object : ObjectId) :
    Except IntegralObjectError IntegralObjectStore := do
  let _ ← store.metadata object
  let objects ← (store.objects.extendTemporary object).mapError IntegralObjectError.lifetime
  pure {store with objects}

/-- Reuse an ended storage slot for a new integral object, retaining its
    storage identity and clearing the old value before initialization. -/
def reuseEnded (store : IntegralObjectStore) (object : ObjectId)
    (type : CppTypeEvidence) : Except IntegralObjectError IntegralObjectStore := do
  let _ ← store.metadata object
  let _ ← formatFor store.profile type
  let objects ← (store.objects.reuseEnded object type).mapError IntegralObjectError.lifetime
  pure {store with objects, values := store.values.modify object (fun _ => none)}

def releaseStorage (store : IntegralObjectStore) (object : ObjectId) :
    Except IntegralObjectError IntegralObjectStore := do
  let _ ← store.metadata object
  let objects ← (store.objects.releaseStorage object).mapError IntegralObjectError.lifetime
  pure {store with objects, values := store.values.modify object (fun _ => none)}


private theorem metadata_bound (store : IntegralObjectStore) (object : ObjectId) (entry : CppObject)
    (h : store.metadata object = .ok entry) : object < store.values.length := by
  unfold metadata at h
  cases hs : store.checkShape with
  | error reason => simp [hs, Bind.bind, Except.bind] at h
  | ok shapeUnit =>
      cases ho : store.objects.object? object with
      | none => simp [hs, ho, Bind.bind, Except.bind] at h
      | some obj =>
          have hlen : store.values.length = store.objects.objects.length := by
            by_cases heq : store.values.length = store.objects.objects.length
            · exact heq
            · by_cases hv : store.profile.valid = true <;>
                simp [checkShape, hv, heq, Bind.bind, Except.bind] at hs
          have hob : object < store.objects.objects.length := by
            have := (List.getElem?_eq_some_iff.mp ho).1
            exact this
          simpa [hlen] using hob

/-- Successful initialization writes the value into its object slot. -/
theorem initializeValue_value (store : IntegralObjectStore) (object : ObjectId) (value : IntegralValue)
    (out : IntegralObjectStore) (h : store.initializeValue object value = .ok out) :
    out.values[object]? = some (some value) := by
  cases hm : store.metadata object with
  | error reason => simp [initializeValue, hm, Bind.bind, Except.bind] at h
  | ok entry =>
    have hbound := metadata_bound store object entry hm
    cases hv : checkValue store.profile entry.type value with
    | error reason => simp [initializeValue, hm, hv, Bind.bind, Except.bind] at h
    | ok u =>
      cases hs : store.objects.beginLifetime object with
      | error reason => simp [initializeValue, hm, hv, hs, Bind.bind, Except.bind, Except.mapError] at h
      | ok started =>
        cases hi : started.initializeObject object with
        | error reason => simp [initializeValue, hm, hv, hs, hi, Bind.bind, Except.bind, Except.mapError] at h
        | ok objects =>
          simp [initializeValue, hm, hv, hs, hi, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure] at h
          subst out
          simp [List.getElem?_eq_getElem hbound]

private theorem metadata_spec (store : IntegralObjectStore) (object : ObjectId) (entry : CppObject)
    (h : store.metadata object = .ok entry) :
    ∃ format, store.checkShape = .ok () ∧ store.objects.object? object = some entry ∧
      formatFor store.profile entry.type = .ok format := by
  cases hs : store.checkShape with
  | error reason => simp [metadata, hs, Bind.bind, Except.bind] at h
  | ok u =>
    cases u
    cases ho : store.objects.object? object with
    | none => simp [metadata, hs, ho, Bind.bind, Except.bind] at h
    | some obj =>
      cases hf : formatFor store.profile obj.type with
      | error reason => simp [metadata, hs, ho, hf, Bind.bind, Except.bind] at h
      | ok format =>
        have he : obj = entry := by
          simpa [metadata, hs, ho, hf, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        subst entry
        exact ⟨format, rfl, rfl, hf⟩

/-- After successful initialization, borrowing the same object and reading it
returns the initialized value. The original object type is retained. -/
theorem initializeValue_read (store : IntegralObjectStore) (object : ObjectId) (value : IntegralValue)
    (out : IntegralObjectStore) (h : store.initializeValue object value = .ok out) :
    ∃ previous, store.objects.object? object = some previous ∧
      out.borrow object = .ok {object := object, type := previous.type} ∧
      out.read {object := object, type := previous.type} = .ok value := by
  cases hm : store.metadata object with
  | error reason => simp [initializeValue, hm, Bind.bind, Except.bind] at h
  | ok entry =>
    obtain ⟨fmt, hshape, hobject, hfmt⟩ := metadata_spec store object entry hm
    have hbound := metadata_bound store object entry hm
    cases hv : checkValue store.profile entry.type value with
    | error reason => simp [initializeValue, hm, hv, Bind.bind, Except.bind] at h
    | ok u =>
      cases u
      cases hs : store.objects.beginLifetime object with
      | error reason => simp [initializeValue, hm, hv, hs, Bind.bind, Except.bind, Except.mapError] at h
      | ok started =>
        cases hi : started.initializeObject object with
        | error reason => simp [initializeValue, hm, hv, hs, hi, Bind.bind, Except.bind, Except.mapError] at h
        | ok objects =>
          obtain ⟨old, hold, hphase, hstartobj, hstartlen⟩ := ObjectStore.beginLifetime_object store.objects object started hs
          have holdEq : old = entry := by simpa [hobject] using hold.symm
          subst old
          obtain ⟨mid, hmid, hmidphase, hnewobj, hnewlen⟩ := ObjectStore.initializeObject_object started object objects hi
          have hmidEq : mid = {entry with phase := .aliveUninitialized} := by simpa [hstartobj] using hmid.symm
          subst mid
          simp [initializeValue, hm, hv, hs, hi, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure] at h
          subst out
          have hvlen : (store.values.modify object (fun _ => some value)).length = objects.objects.length := by
            have hlen : store.values.length = store.objects.objects.length := by
              by_cases heq : store.values.length = store.objects.objects.length
              · exact heq
              · by_cases hp : store.profile.valid = true <;>
                  simp [checkShape, hp, heq, Bind.bind, Except.bind] at hshape
            simpa [hnewlen, hstartlen] using hlen
          have hlen' : store.values.length = store.objects.objects.length := by
            simpa [hnewlen, hstartlen] using hvlen
          have houtshape : ({store with objects := objects, values := store.values.modify object (fun _ => some value)} : IntegralObjectStore).checkShape = .ok () := by
            simpa [checkShape, hvlen, hlen'] using hshape
          have houtmeta : ({store with objects := objects, values := store.values.modify object (fun _ => some value)} : IntegralObjectStore).metadata object =
              .ok {entry with phase := .aliveInitialized} := by
            simp [metadata, houtshape, hnewobj, hfmt, Bind.bind, Except.bind, Pure.pure, Except.pure]
          have hvalues : (store.values.modify object (fun _ => some value))[object]? = some (some value) := by
            simp [List.getElem?_eq_getElem hbound]
          have hreadtype : objects.readType object = .ok entry.type := by
            simp [ObjectStore.readType, hnewobj]
          cases hd : descriptor entry.type with
          | error reason => simp [formatFor, hd, Bind.bind, Except.bind] at hfmt
          | ok desc =>
            rcases desc with ⟨kind, isConst⟩
            have hkind : (kind == kind) = true := by cases kind <;> rfl
            refine ⟨entry, hobject, ?_, ?_⟩
            · simp [borrow, houtmeta, requireAlive, Bind.bind, Except.bind, Pure.pure, Except.pure]
            · simp [read, validateAccess, houtmeta, hd, hkind, requireAlive, hreadtype, hvalues, hv,
                Bind.bind, Except.bind, Pure.pure, Except.pure, Except.mapError]


/-- Successful allocation exposes fresh storage with the requested type. -/
theorem allocate_object (store : IntegralObjectStore) (duration : StorageDuration) (type : CppTypeEvidence)
    (out : IntegralObjectStore) (object : ObjectId) (h : store.allocate duration type = .ok (out, object)) :
    out.objects.object? object = some {duration := duration, type := type, phase := .storageOnly} := by
  cases hc : store.checkShape with
  | error reason => simp [allocate, hc, Bind.bind, Except.bind] at h
  | ok u =>
    cases hf : formatFor store.profile type with
    | error reason => simp [allocate, hc, hf, Bind.bind, Except.bind] at h
    | ok fmt =>
      simp [allocate, hc, hf, Bind.bind, Except.bind, Pure.pure, Except.pure, ObjectStore.allocate] at h
      rcases h with ⟨rfl, rfl⟩
      simp [ObjectStore.object?]

end IntegralObjectStore

end LeanModels.Cpp
