import LeanModels.Cpp.IntegralObjects

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

def automaticInitializedDeclaration : Bool :=
  match IntegralObjectStore.empty .lp64 with
  | .error _ => false
  | .ok store =>
      match store.declareAutomaticInitialized (.builtin .int) (.builtin .short)
          ⟨.signed 16, 7⟩ with
      | .error _ => false
      | .ok (initialized, object) =>
          match initialized.borrow object with
          | .error _ => false
          | .ok access =>
              match initialized.read access, initialized.endLifetime object with
              | .ok value, .ok ended =>
                  value.value == 7 &&
                    (ended.read access matches .error (.lifetime .lifetimeEnded))
              | _, _ => false

#guard automaticDeclarationLifecycle
#guard automaticInitializedDeclaration

theorem automatic_declaration_lifecycle : automaticDeclarationLifecycle = true := by
  rfl

theorem automatic_initialized_declaration : automaticInitializedDeclaration = true := by
  rfl

#print axioms automatic_declaration_lifecycle
#print axioms automatic_initialized_declaration

end LeanModels.Cpp.ObjectModelRung1Tests
