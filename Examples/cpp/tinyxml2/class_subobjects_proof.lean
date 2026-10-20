import Examples.cpp.tinyxml2.ElementHierarchy
import Examples.cpp.tinyxml2.DocumentHierarchy
import Examples.cpp.tinyxml2.BaseGetLineNum

namespace Examples.cpp.tinyxml2
open LeanModels.Cpp

private def receiver (hierarchy : ClassHierarchy) (objects : List ObjectId)
    (path : List Nat) (snapshot : IntegralMemberSnapshot) : ClassReceiverProjection :=
  ⟨hierarchy, objects, path, snapshot⟩

/-- The original XMLNode getter runs on the base subobject of an actual
XMLElement hierarchy, preserving the entire caller memory. -/
theorem element_base_returns (objects : List ObjectId) (path : List Nat)
    (state : IntegralMemberSnapshot) (access : IntegralObjectRef) (value : IntegralValue)
    (checked : (receiver ElementHierarchy.hierarchy objects path state).check BaseGetLineNum.getter = .ok ())
    (bound : state.bind BaseGetLineNum.getter = .ok access)
    (read : state.memory.read access = .ok value) :
    (receiver ElementHierarchy.hierarchy objects path state).invoke BaseGetLineNum.getter =
      .ok (state.memory, value) :=
  ClassReceiverProjection.invoke_of_check _ _ _ _ checked
    (IntegralMemberGetter.invoke_of_read _ _ _ _ _ (by decide) bound read rfl)

/-- XMLDocument supplies a different concrete complete-object class with the
same abstract XMLNode base declaration and original selected getter body. -/
theorem document_base_returns (objects : List ObjectId) (path : List Nat)
    (state : IntegralMemberSnapshot) (access : IntegralObjectRef) (value : IntegralValue)
    (checked : (receiver DocumentHierarchy.hierarchy objects path state).check BaseGetLineNum.getter = .ok ())
    (bound : state.bind BaseGetLineNum.getter = .ok access)
    (read : state.memory.read access = .ok value) :
    (receiver DocumentHierarchy.hierarchy objects path state).invoke BaseGetLineNum.getter =
      .ok (state.memory, value) :=
  ClassReceiverProjection.invoke_of_check _ _ _ _ checked
    (IntegralMemberGetter.invoke_of_read _ _ _ _ _ (by decide) bound read rfl)

private def observed (hierarchy : ClassHierarchy) : Option Int := do
  let slots ← hierarchy.slots.toOption
  let some (_, index) := slots.zipIdx.find? (fun (slot, _) => slot.path == [0]) | none
  let getter := BaseGetLineNum.getter
  let projection : ClassReceiverProjection := {
    hierarchy, objects := List.range slots.length, receiverPath := [0],
    snapshot := {
      memory := {
        profile := .lp64,
        objects := {objects := slots.map (fun slot =>
          ⟨.automatic, .record slot.declaration, .aliveInitialized⟩) ++
          [⟨.automatic, getter.field.type, .aliveInitialized⟩]},
        values := slots.map (fun _ => none) ++ [some ⟨.signed 32, 7⟩]},
      object := index, member := slots.length, field := getter.field.declaration}}
  match projection.invoke getter with
  | .ok (memory, value) => if memory == projection.snapshot.memory then some value.value else none
  | _ => none

private theorem live_base_examples :
    observed ElementHierarchy.hierarchy = some 7 ∧
    observed DocumentHierarchy.hierarchy = some 7 ∧
    (ElementHierarchy.hierarchy.classes.find? (·.declaration == BaseGetLineNum.getter.owner)).map
      (·.isAbstract) = some true := by decide

#print axioms element_base_returns
#print axioms document_base_returns
#print axioms live_base_examples
end Examples.cpp.tinyxml2
