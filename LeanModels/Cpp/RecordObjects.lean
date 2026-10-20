import LeanModels.Cpp.RecordEvidence
import LeanModels.Cpp.IntegralObjects

namespace LeanModels.Cpp

structure IntegralRecordInstance where
  object : ObjectId
  schema : IntegralRecordSchema
  members : List ObjectId
  isConst : Bool
  deriving Repr, BEq, Inhabited

structure IntegralRecordRef where
  object : ObjectId
  declaration : FrontendHandle
  readOnly : Bool := false
  deriving Repr, BEq, Inhabited

structure IntegralRecordStore where
  memory : IntegralObjectStore
  records : List IntegralRecordInstance
  deriving Repr, BEq, Inhabited

inductive IntegralRecordError where
  | integral (reason : IntegralObjectError)
  | object (reason : ObjectError)
  | invalidSchema
  | incoherentStore
  | arityMismatch
  | missingRecord (object : ObjectId)
  | wrongRecordType
  | missingMember (declaration : FrontendHandle)
  deriving Repr, BEq, Inhabited

namespace IntegralRecordStore

private def recordType (schema : IntegralRecordSchema) (constant : Bool) : CppTypeEvidence :=
  if constant then .qualified true false (.record schema.declaration) else .record schema.declaration

private def fieldType (field : IntegralRecordField) (constant : Bool) : CppTypeEvidence :=
  if constant && !field.isMutable then .qualified true false field.type else field.type

private def memberPhase (root member : ObjectPhase) : Bool :=
  match root with
  | .aliveInitialized => member == .aliveInitialized
  | .ended => member == .ended
  | .released => member == .released
  | _ => false

private def scalarCellValid (profile : TargetProfile) (object : CppObject)
    (value : Option IntegralValue) : Bool :=
  match recordIntegralKind object.type with
  | none => false
  | some (kind, _) =>
      if object.phase == .aliveInitialized then
        match value, profile.format kind with
        | some value, .ok format => value.invalid?.isNone && value.format == format
        | _, _ => false
      else value.isNone && (object.phase != .released || object.duration == .dynamic)

private def schemasCompatible (first second : IntegralRecordSchema) : Bool :=
  if first.declaration == second.declaration then first == second
  else first.fields.all (fun field => field.declaration != second.declaration &&
    second.fields.all (fun other => field.declaration != other.declaration)) &&
    second.fields.all (fun field => field.declaration != first.declaration)

/-- Check complete-object ownership, scalar values and lifetime coherence. -/
def check (store : IntegralRecordStore) : Except IntegralRecordError Unit := do
  unless store.memory.profile.valid &&
      store.memory.values.length == store.memory.objects.objects.length do throw .incoherentStore
  let roots := store.records.map (·.object)
  let owned := store.records.flatMap (fun record => record.object :: record.members)
  unless owned.eraseDups.length == owned.length do throw .incoherentStore
  for record in store.records do
    unless record.schema.valid && record.members.length == record.schema.fields.length &&
        store.records.all (fun other => schemasCompatible record.schema other.schema) do
      throw .incoherentStore
    let some root := store.memory.objects.object? record.object | throw .incoherentStore
    unless root.type == recordType record.schema record.isConst &&
        store.memory.values[record.object]? == some none do throw .incoherentStore
    unless root.phase == .aliveInitialized || root.phase == .ended || root.phase == .released do
      throw .incoherentStore
    if root.phase == .released && root.duration != .dynamic then throw .incoherentStore
    for (field, member) in record.schema.fields.zip record.members do
      let some object := store.memory.objects.object? member | throw .incoherentStore
      unless object.type == fieldType field record.isConst && object.duration == root.duration &&
          memberPhase root.phase object.phase do throw .incoherentStore
      if object.phase == .ended || object.phase == .released then
        unless store.memory.values[member]? == some none do throw .incoherentStore
  for (object, index) in store.memory.objects.objects.zipIdx do
    unless roots.contains index || scalarCellValid store.memory.profile object
        (store.memory.values[index]?.getD none) do throw .incoherentStore

private def findRecord (store : IntegralRecordStore) (access : IntegralRecordRef) :
    Except IntegralRecordError IntegralRecordInstance := do
  store.check
  let some record := store.records.find? (·.object == access.object)
    | throw (.missingRecord access.object)
  unless record.schema.declaration == access.declaration do throw .wrongRecordType
  pure record

private def requireAlive (store : IntegralRecordStore) (record : IntegralRecordInstance) :
    Except IntegralRecordError Unit := do
  let _ ← (store.memory.objects.readType record.object).mapError IntegralRecordError.object

def empty (profile : TargetProfile) : Except IntegralRecordError IntegralRecordStore := do
  let memory ← (IntegralObjectStore.empty profile).mapError IntegralRecordError.integral
  pure {memory, records := []}

/-- Import a caller's ordinary integral memory. No record object is invented. -/
def fromMemory (memory : IntegralObjectStore) : Except IntegralRecordError IntegralRecordStore := do
  let store := {memory, records := [] : IntegralRecordStore}
  store.check
  pure store

/-- Check a returned callee memory before rejoining it to record ownership. -/
def acceptMemory (store : IntegralRecordStore) (memory : IntegralObjectStore) :
    Except IntegralRecordError IntegralRecordStore := do
  unless memory.profile == store.memory.profile &&
      (store.records.flatMap (fun record => record.object :: record.members)).all
        (fun object => memory.objects.object? object == store.memory.objects.object? object) do
    throw .incoherentStore
  let updated := {store with memory}
  updated.check
  pure updated

private def validateValue (profile : TargetProfile) (field : IntegralRecordField)
    (value : IntegralValue) : Except IntegralRecordError Unit := do
  let some (kind, _) := recordIntegralKind field.type | throw .invalidSchema
  let format ← match profile.format kind with
    | .ok format => pure format
    | .error _ => throw (.integral .invalidProfile)
  if let some reason := value.invalid? then throw (.integral (.invalidValue reason))
  unless value.format == format do throw (.integral .valueTypeMismatch)

/-- Allocate a complete object and its initialized integral members from
    already evaluated values. No constructor or aggregate expression is run. -/
def create (store : IntegralRecordStore) (schema : IntegralRecordSchema)
    (duration : StorageDuration) (values : List IntegralValue) (isConst : Bool := false) :
    Except IntegralRecordError (IntegralRecordStore × IntegralRecordRef) := do
  store.check
  unless schema.valid do throw .invalidSchema
  unless values.length == schema.fields.length do throw .arityMismatch
  for (field, value) in schema.fields.zip values do validateValue store.memory.profile field value
  let (objects, object) := store.memory.objects.allocate duration (recordType schema isConst)
  let objects ← (objects.beginLifetime object).mapError IntegralRecordError.object
  let mut memory := {store.memory with objects, values := store.memory.values ++ [none]}
  let mut members := []
  for (field, value) in schema.fields.zip values do
    let (allocated, member) ← (memory.allocate duration (fieldType field isConst)).mapError IntegralRecordError.integral
    memory ← (allocated.initializeValue member value).mapError IntegralRecordError.integral
    members := members ++ [member]
  let objects ← (memory.objects.initializeObject object).mapError IntegralRecordError.object
  let updated := {
    memory := {memory with objects},
    records := store.records ++ [{object, schema, members, isConst}] : IntegralRecordStore}
  updated.check
  pure (updated, {object, declaration := schema.declaration, readOnly := isConst})

/-- A record view adds const access without changing actual member metadata. -/
def borrow (store : IntegralRecordStore) (object : ObjectId) (readOnly : Bool := false) :
    Except IntegralRecordError IntegralRecordRef := do
  store.check
  let some record := store.records.find? (·.object == object) | throw (.missingRecord object)
  requireAlive store record
  pure {object, declaration := record.schema.declaration, readOnly := readOnly || record.isConst}

/-- Projection does not read, allocate, or copy the member. -/
def memberRef (store : IntegralRecordStore) (access : IntegralRecordRef)
    (declaration : FrontendHandle) : Except IntegralRecordError IntegralObjectRef := do
  let record ← findRecord store access
  requireAlive store record
  let some (field, member) := (record.schema.fields.zip record.members).find?
      (fun (field, _) => field.declaration == declaration) | throw (.missingMember declaration)
  (store.memory.borrow member (access.readOnly && !field.isMutable)).mapError IntegralRecordError.integral

def readMember (store : IntegralRecordStore) (access : IntegralRecordRef)
    (declaration : FrontendHandle) : Except IntegralRecordError IntegralValue := do
  let member ← store.memberRef access declaration
  (store.memory.read member).mapError IntegralRecordError.integral

def assignMember (store : IntegralRecordStore) (access : IntegralRecordRef)
    (declaration : FrontendHandle) (value : IntegralValue) :
    Except IntegralRecordError IntegralRecordStore := do
  let member ← store.memberRef access declaration
  let memory ← (store.memory.assign member value).mapError IntegralRecordError.integral
  pure {store with memory}

/-- End all members as well as their complete object; integral aliases go stale. -/
def endLifetime (store : IntegralRecordStore) (access : IntegralRecordRef) :
    Except IntegralRecordError IntegralRecordStore := do
  let record ← findRecord store access
  requireAlive store record
  let mut memory := store.memory
  for member in record.members.reverse do
    memory ← (memory.endLifetime member).mapError IntegralRecordError.integral
  let objects ← (memory.objects.endLifetime record.object).mapError IntegralRecordError.object
  let updated := {store with memory := {memory with objects}}
  updated.check
  pure updated

def releaseStorage (store : IntegralRecordStore) (access : IntegralRecordRef) :
    Except IntegralRecordError IntegralRecordStore := do
  let record ← findRecord store access
  -- The ordinary object gate enforces dynamic duration and ended lifetime.
  let objects ← (store.memory.objects.releaseStorage record.object).mapError IntegralRecordError.object
  let mut memory := {store.memory with objects}
  for member in record.members.reverse do
    memory ← (memory.releaseStorage member).mapError IntegralRecordError.integral
  let updated := {store with memory}
  updated.check
  pure updated

/-- Rejoining a callee memory preserves every ownership declaration and identity. -/
theorem acceptMemory_records (store : IntegralRecordStore) (memory : IntegralObjectStore)
    (updated : IntegralRecordStore) (h : store.acceptMemory memory = .ok updated) :
    updated.records = store.records := by
  unfold acceptMemory at h
  split at h
  · change (do
      ({store with memory} : IntegralRecordStore).check
      pure ({store with memory} : IntegralRecordStore)) = .ok updated at h
    cases hc : ({store with memory} : IntegralRecordStore).check with
    | error reason =>
        simp only [hc] at h
        change Except.error reason = Except.ok updated at h
        cases h
    | ok result =>
        cases result
        simp [hc] at h
        cases h
        rfl
  · change Except.error IntegralRecordError.incoherentStore = Except.ok updated at h
    cases h

end IntegralRecordStore
end LeanModels.Cpp
