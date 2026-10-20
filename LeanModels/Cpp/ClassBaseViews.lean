import LeanModels.Cpp.ClassSubobjects

namespace LeanModels.Cpp

/-- An existing-object nonvirtual base view. Paths identify occurrences in the
closed hierarchy; no ABI offset, allocation, dynamic cast or source access
check is inferred here. -/
structure ClassBaseView where
  hierarchy : ClassHierarchy
  objects : List ObjectId
  sourcePath : List Nat
  targetPath : List Nat
  memory : IntegralObjectStore
  deriving Repr, BEq, Inhabited

inductive ClassBaseViewError where
  | hierarchy (reason : String)
  | malformedWorld
  | missingSource
  | missingTarget
  | nonBasePath
  | sameSubobject
  deriving Repr, BEq, Inhabited

namespace ClassBaseView

private def isPrefix : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | first :: rest, other :: tail => first == other && isPrefix rest tail

private def slotAt (slots : List ClassSubobjectSlot) (path : List Nat) :
    Option (ClassSubobjectSlot × ObjectId) :=
  (slots.zipIdx.find? (fun (slot, _) => slot.path == path)).map
    (fun (slot, index) => (slot, index))

private def hierarchySlots (hierarchy : ClassHierarchy) :
    Except ClassBaseViewError (List ClassSubobjectSlot) :=
  match hierarchy.slots with
  | .ok slots => .ok slots
  | .error reason => .error (.hierarchy reason)

/-- Validate the complete root and every supplied nonvirtual occurrence before
    allowing a source-prefix view to select its target identity. -/
def check (view : ClassBaseView) : Except ClassBaseViewError Unit := do
  let slots ← hierarchySlots view.hierarchy
  unless view.objects.length == slots.length &&
      view.objects.eraseDups.length == view.objects.length &&
      view.memory.values.length == view.memory.objects.objects.length do
    throw .malformedWorld
  let some rootId := view.objects.head? | throw .malformedWorld
  let rootType ← (view.memory.objects.readType rootId).mapError (fun _ => .malformedWorld)
  let constant ← match rootType with
    | .record name =>
        unless name == view.hierarchy.root do throw .malformedWorld
        pure false
    | .qualified true false (.record name) =>
        unless name == view.hierarchy.root do throw .malformedWorld
        pure true
    | _ => throw .malformedWorld
  let some root := view.memory.objects.object? rootId | throw .malformedWorld
  for (slot, objectId) in slots.zip view.objects do
    let type ← (view.memory.objects.readType objectId).mapError (fun _ => .malformedWorld)
    let some object := view.memory.objects.object? objectId | throw .malformedWorld
    unless type == integralMemberViewType (.record slot.declaration) constant &&
        object.duration == root.duration && object.phase == .aliveInitialized &&
        view.memory.values[objectId]? == some none do
      throw .malformedWorld
  let some (source, sourceId) := slotAt slots view.sourcePath | throw .missingSource
  let some (target, targetId) := slotAt slots view.targetPath | throw .missingTarget
  unless source.path != target.path && isPrefix source.path target.path do
    throw .nonBasePath
  unless sourceId != targetId && source.declaration != target.declaration do
    throw .sameSubobject

def convert (view : ClassBaseView) :
    Except ClassBaseViewError (IntegralObjectStore × ObjectId) := do
  match view.check with
  | .error reason => .error reason
  | .ok _ =>
      match hierarchySlots view.hierarchy with
      | .error reason => .error reason
      | .ok slots =>
          match slotAt slots view.targetPath with
          | none => .error .missingTarget
          | some (_, targetId) => .ok (view.memory, targetId)

theorem convert_of_check (view : ClassBaseView) (memory : IntegralObjectStore)
    (object : ObjectId) (checked : view.check = .ok ())
    (target : view.convert = .ok (memory, object)) :
    memory = view.memory := by
  unfold convert at target
  rw [checked] at target
  cases hs : hierarchySlots view.hierarchy with
  | error reason => simp [hs] at target
  | ok slots =>
      cases ht : slotAt slots view.targetPath with
      | none => simp [hs, ht] at target
      | some pair =>
          simp [hs, ht] at target
          exact target.1.symm

theorem convert_memory (view : ClassBaseView) (memory : IntegralObjectStore)
    (object : ObjectId) (h : view.convert = .ok (memory, object)) :
    memory = view.memory := by
  unfold convert at h
  cases hc : view.check with
  | error reason => simp [hc] at h
  | ok result =>
      cases hs : hierarchySlots view.hierarchy with
      | error reason => simp [hc, hs] at h
      | ok slots =>
          cases ht : slotAt slots view.targetPath with
          | none => simp [hc, hs, ht] at h
          | some pair =>
              simp [hc, hs, ht] at h
              exact h.1.symm

end ClassBaseView
end LeanModels.Cpp
