import LeanModels.Cpp.TypeEvidence

namespace LeanModels.Cpp

abbrev ObjectId := Nat

inductive StorageDuration where
  | static_
  | thread
  | automatic
  | dynamic
  deriving Repr, BEq, Inhabited

inductive ObjectPhase where
  | storageOnly
  | aliveUninitialized
  | aliveInitialized
  | ended
  | released
  deriving Repr, BEq, Inhabited

inductive ObjectError where
  | missing (object : ObjectId)
  | lifetimeNotStarted
  | notInitialized
  | alreadyStarted
  | alreadyInitialized
  | lifetimeEnded
  | storageReleased
  | dynamicStorageLive
  | notDynamicStorage
  deriving Repr, BEq, Inhabited

structure CppObject where
  duration : StorageDuration
  type : CppTypeEvidence
  phase : ObjectPhase
  deriving Repr, BEq, Inhabited

structure ObjectStore where
  objects : List CppObject
  deriving Repr, BEq, Inhabited

namespace ObjectStore

def empty : ObjectStore := ⟨[]⟩

def object? (store : ObjectStore) (object : ObjectId) : Option CppObject :=
  store.objects[object]?

def allocate (store : ObjectStore) (duration : StorageDuration)
    (type : CppTypeEvidence) : ObjectStore × ObjectId :=
  (⟨store.objects ++ [{duration, type, phase := .storageOnly}]⟩, store.objects.length)

private def update (store : ObjectStore) (object : ObjectId)
    (change : CppObject → CppObject) : Except ObjectError ObjectStore :=
  match store.object? object with
  | none => .error (.missing object)
  | some _ => .ok {objects := store.objects.modify object change}

def beginLifetime (store : ObjectStore) (object : ObjectId) : Except ObjectError ObjectStore :=
  match store.object? object with
  | none => .error (.missing object)
  | some value =>
      match value.phase with
      | .storageOnly => update store object fun current =>
          {current with phase := .aliveUninitialized}
      | .aliveUninitialized | .aliveInitialized => .error .alreadyStarted
      | .ended => .error .lifetimeEnded
      | .released => .error .storageReleased

/-- Rung-1 automatic declaration boundary: reserve automatic storage and start
    the object's lifetime, leaving initialization as a separate operation. -/
def declareAutomatic (store : ObjectStore) (type : CppTypeEvidence) :
    ObjectStore × ObjectId :=
  let (reserved, object) := store.allocate .automatic type
  match reserved.beginLifetime object with
  | .ok live => (live, object)
  | .error _ => (reserved, object)

def initializeObject (store : ObjectStore) (object : ObjectId) : Except ObjectError ObjectStore :=
  match store.object? object with
  | none => .error (.missing object)
  | some value =>
      match value.phase with
      | .storageOnly => .error .lifetimeNotStarted
      | .aliveUninitialized => update store object fun current =>
          {current with phase := .aliveInitialized}
      | .aliveInitialized => .error .alreadyInitialized
      | .ended => .error .lifetimeEnded
      | .released => .error .storageReleased

def endLifetime (store : ObjectStore) (object : ObjectId) : Except ObjectError ObjectStore :=
  match store.object? object with
  | none => .error (.missing object)
  | some value =>
      match value.phase with
      | .storageOnly => .error .lifetimeNotStarted
      | .aliveUninitialized | .aliveInitialized => update store object fun current =>
          {current with phase := .ended}
      | .ended => .error .lifetimeEnded
      | .released => .error .storageReleased

def releaseStorage (store : ObjectStore) (object : ObjectId) : Except ObjectError ObjectStore :=
  match store.object? object with
  | none => .error (.missing object)
  | some value =>
      match value.phase, value.duration with
      | .ended, .dynamic => update store object fun current =>
          {current with phase := .released}
      | .storageOnly, _ => .error .lifetimeNotStarted
      | .aliveUninitialized, _ | .aliveInitialized, _ => .error .dynamicStorageLive
      | .ended, _ => .error .notDynamicStorage
      | .released, _ => .error .storageReleased

def readType (store : ObjectStore) (object : ObjectId) : Except ObjectError CppTypeEvidence :=
  match store.object? object with
  | none => .error (.missing object)
  | some value =>
      match value.phase with
      | .aliveInitialized => .ok value.type
      | .storageOnly => .error .lifetimeNotStarted
      | .aliveUninitialized => .error .notInitialized
      | .ended => .error .lifetimeEnded
      | .released => .error .storageReleased

end ObjectStore

end LeanModels.Cpp
