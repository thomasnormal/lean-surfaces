import LeanModels.Cpp.ObjectModel

namespace LeanModels.Cpp.ObjectModelRung1Tests

open LeanModels.Cpp

def intType : CppTypeEvidence := .builtin .int

def automaticDeclarationLifecycle : Bool :=
  let (live, object) := ObjectStore.declareAutomatic ObjectStore.empty intType
  match live.object? object with
  | some entry =>
      entry.duration == .automatic && entry.phase == .aliveUninitialized &&
      match live.initializeObject object with
      | .ok initialized =>
          match initialized.endLifetime object with
          | .ok ended =>
              (ended.readType object matches .error .lifetimeEnded)
          | .error _ => false
      | .error _ => false
  | none => false

#guard automaticDeclarationLifecycle

theorem automatic_declaration_lifecycle : automaticDeclarationLifecycle = true := by
  rfl

#print axioms automatic_declaration_lifecycle

end LeanModels.Cpp.ObjectModelRung1Tests
