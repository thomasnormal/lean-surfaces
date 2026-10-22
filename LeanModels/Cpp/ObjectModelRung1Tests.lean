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

def automaticAssignmentLifecycle : Bool :=
  match IntegralObjectStore.empty .lp64 with
  | .error _ => false
  | .ok store =>
      match store.declareAutomaticInitialized (.builtin .int) (.builtin .short)
          ⟨.signed 16, 7⟩ with
      | .error _ => false
      | .ok (initialized, object) =>
          match initialized.borrow object, initialized.borrow object true with
          | .ok access, .ok readOnly =>
              match initialized.read access,
                    initialized.assignConverted access (.builtin .short) ⟨.signed 16, 11⟩ with
              | .ok before, .ok assigned =>
                  match assigned.read access,
                        assigned.assignConverted readOnly (.builtin .short) ⟨.signed 16, 13⟩,
                        assigned.endLifetime object with
                  | .ok after, .error .constWrite, .ok ended =>
                      before.value == 7 && after.value == 11 &&
                        (ended.read access matches .error (.lifetime .lifetimeEnded)) &&
                        (ended.assignConverted access (.builtin .short) ⟨.signed 16, 17⟩
                          matches .error (.lifetime .lifetimeEnded))
                  | _, _, _ => false
              | _, _ => false
          | _, _ => false

#guard automaticDeclarationLifecycle
#guard automaticInitializedDeclaration
#guard automaticAssignmentLifecycle

theorem automatic_declaration_lifecycle : automaticDeclarationLifecycle = true := by
  rfl

theorem automatic_initialized_declaration : automaticInitializedDeclaration = true := by
  rfl

theorem automatic_assignment_lifecycle : automaticAssignmentLifecycle = true := by
  rfl

#print axioms automatic_declaration_lifecycle
#print axioms automatic_initialized_declaration
#print axioms automatic_assignment_lifecycle

end LeanModels.Cpp.ObjectModelRung1Tests
