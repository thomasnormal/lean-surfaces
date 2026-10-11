import LeanModels.Cpp.ObjectModel

namespace LeanModels.Cpp.ObjectModelTests

open LeanModels.Cpp

def intType : CppTypeEvidence := .builtin .int

def automatic : ObjectStore × ObjectId :=
  ObjectStore.allocate ObjectStore.empty .automatic intType

def dynamic : ObjectStore × ObjectId :=
  ObjectStore.allocate ObjectStore.empty .dynamic intType

#guard automatic.2 == 0
#guard (ObjectStore.readType automatic.1 automatic.2) matches .error .lifetimeNotStarted
#guard (ObjectStore.beginLifetime automatic.1 automatic.2).isOk
#guard match ObjectStore.beginLifetime automatic.1 automatic.2 with
  | .ok store => ((ObjectStore.readType store automatic.2) matches .error .notInitialized)
  | .error _ => false
#guard match ObjectStore.beginLifetime automatic.1 automatic.2 with
  | .ok store =>
      match ObjectStore.initializeObject store automatic.2 with
      | .ok initialized =>
          ((ObjectStore.readType initialized automatic.2) matches .ok (.builtin .int))
      | .error _ => false
  | .error _ => false
#guard match ObjectStore.beginLifetime automatic.1 automatic.2 with
  | .ok store => ((ObjectStore.beginLifetime store automatic.2) matches .error .alreadyStarted)
  | .error _ => false
#guard match ObjectStore.beginLifetime automatic.1 automatic.2 with
  | .ok store =>
      match ObjectStore.initializeObject store automatic.2 with
      | .ok initialized =>
          match ObjectStore.endLifetime initialized automatic.2 with
          | .ok ended =>
              ((ObjectStore.readType ended automatic.2) matches .error .lifetimeEnded)
          | .error _ => false
      | .error _ => false
  | .error _ => false
#guard match ObjectStore.beginLifetime dynamic.1 dynamic.2 with
  | .ok live =>
      ((ObjectStore.releaseStorage live dynamic.2) matches .error .dynamicStorageLive)
  | .error _ => false
#guard match ObjectStore.beginLifetime dynamic.1 dynamic.2 with
  | .ok live =>
      match ObjectStore.initializeObject live dynamic.2 with
      | .ok initialized =>
          match ObjectStore.endLifetime initialized dynamic.2 with
          | .ok ended =>
              match ObjectStore.releaseStorage ended dynamic.2 with
              | .ok released =>
                  ((ObjectStore.readType released dynamic.2) matches .error .storageReleased)
              | .error _ => false
          | .error _ => false
      | .error _ => false
  | .error _ => false
#guard (ObjectStore.beginLifetime ObjectStore.empty 3) matches .error (.missing 3)
#guard match ObjectStore.allocate automatic.1 .static_ intType with
  | (store, object) =>
      match ObjectStore.beginLifetime store object with
      | .ok live =>
          match ObjectStore.initializeObject live object with
          | .ok initialized =>
              match ObjectStore.endLifetime initialized object with
              | .ok ended =>
                  ((ObjectStore.releaseStorage ended object) matches .error .notDynamicStorage)
              | .error _ => false
          | .error _ => false
      | .error _ => false

end LeanModels.Cpp.ObjectModelTests
