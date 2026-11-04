import Examples.cpp.tinyxml2.ElementHierarchy
import Examples.cpp.tinyxml2.DocumentHierarchy
import Examples.cpp.tinyxml2.BaseGetLineNum
import LeanModels.Cpp.ClassBaseViews

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

private def baseView (hierarchy : ClassHierarchy) : Option (ClassBaseView × ObjectId) := do
  let slots ← hierarchy.slots.toOption
  let some (_, index) := slots.zipIdx.find? (fun (slot, _) => slot.path == [0]) | none
  let candidate : ClassBaseView := {
    hierarchy, objects := List.range slots.length, sourcePath := [], targetPath := [0],
    memory := {
      profile := .lp64,
      objects := {objects := slots.map (fun slot =>
        ⟨.automatic, .record slot.declaration, .aliveInitialized⟩)},
      values := slots.map (fun _ => none)}}
  pure (candidate, index)

private theorem original_base_views :
    (baseView ElementHierarchy.hierarchy).bind (fun (view, _) =>
      view.convert.toOption.map (fun (_, object) => object)) = some 1 ∧
    (baseView DocumentHierarchy.hierarchy).bind (fun (view, _) =>
      view.convert.toOption.map (fun (_, object) => object)) = some 1 := by decide

private def originalCast (hierarchy : ClassHierarchy) : Option ObjectId := do
  let (view, _) ← baseView hierarchy
  let some target := hierarchy.classes[1]? | none
  let cast : ClassBaseCast := {
    view, sourceDeclaration := hierarchy.root,
    targetDeclaration := target.declaration}
  let (memory, object) ← cast.execute.toOption
  if memory == view.memory then some object else none

private theorem original_base_casts :
    originalCast ElementHierarchy.hierarchy = some 1 ∧
    originalCast DocumentHierarchy.hierarchy = some 1 := by decide

private theorem original_friend_shapes :
    ElementHierarchy.hierarchy.classes[0]?.map (·.friends.length) = some 1 ∧
    ElementHierarchy.hierarchy.classes[1]?.map (·.friends.length) = some 2 ∧
    DocumentHierarchy.hierarchy.classes[0]?.map (·.friends.length) = some 6 := by decide

#print axioms element_base_returns
#print axioms document_base_returns
#print axioms live_base_examples
#print axioms original_base_views
#print axioms original_friend_shapes
#print axioms original_base_casts
end Examples.cpp.tinyxml2
