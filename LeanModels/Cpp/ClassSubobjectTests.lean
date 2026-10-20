import LeanModels.Cpp.ClassSubobjects

namespace LeanModels.Cpp.ClassSubobjectTests

private def h (name : String) : FrontendHandle := ⟨name⟩
private def hierarchy : ClassHierarchy := {
  root := h "D", classes := [
    ⟨h "D", false, [h "L", h "R"], []⟩,
    ⟨h "L", true, [h "B"], []⟩,
    ⟨h "R", true, [h "B"], []⟩,
    ⟨h "B", true, [], [h "value"]⟩]}

private def getter (mutable_ : Bool := false) : IntegralMemberGetter := {
  occurrence := default, owner := h "B",
  field := ⟨h "value", "value", .builtin .int, mutable_⟩,
  isConst := true, conversions := [], result := .int}

private def projection (right : Bool := false) (constant : Bool := false)
    (mutable_ : Bool := false) : ClassReceiverProjection := {
  hierarchy, objects := [0, 1, 2, 3, 4],
  receiverPath := if right then [1, 0] else [0, 0],
  snapshot := {
    memory := {
      profile := .lp64,
      objects := {objects :=
        [h "D", h "L", h "B", h "R", h "B"].map (fun name =>
          ⟨.automatic, integralMemberViewType (.record name) constant, .aliveInitialized⟩) ++
        [⟨.automatic, integralMemberViewType (.builtin .int) (constant && !mutable_), .aliveInitialized⟩,
         ⟨.automatic, integralMemberViewType (.builtin .int) (constant && !mutable_), .aliveInitialized⟩]},
      values := [none, none, none, none, none, some ⟨.signed 32, -9⟩, some ⟨.signed 32, 8⟩]},
    object := if right then 4 else 2, member := if right then 6 else 5, field := h "value"}}

private def observed (projection : ClassReceiverProjection) (getter : IntegralMemberGetter := getter) :
    Option Int :=
  match projection.invoke getter with
  | .ok (memory, value) => if memory == projection.snapshot.memory then some value.value else none
  | _ => none

private def change (projection : ClassReceiverProjection) (id : ObjectId)
    (f : CppObject → CppObject) : ClassReceiverProjection :=
  {projection with snapshot := {projection.snapshot with memory :=
    {projection.snapshot.memory with objects :=
      {objects := projection.snapshot.memory.objects.objects.modify id f}}}}

set_option maxRecDepth 10000 in
private theorem kernelSubobjects :
    [
    observed projection == some (-9),
    observed (projection true) == some 8,
    observed (projection false true) == some (-9),
    observed (projection false true true) (getter true) == some (-9),
    observed {projection with objects := [0, 1, 2, 3, 2]} == none,
    observed {projection with objects := [0, 1, 2, 3]} == none,
    observed {projection with receiverPath := [9]} == none,
    observed {projection with receiverPath := []} == none,
    observed {projection with receiverPath := [1, 0]} == none,
    observed {projection with snapshot := {projection.snapshot with member := 3}} == none,
    observed {projection with snapshot := {projection.snapshot with object := 4}} == none,
    observed (change projection 0 (fun object => {object with phase := .ended})) == none,
    observed (change projection 1 (fun object => {object with phase := .released})) == none,
    observed (change projection 3 (fun object => {object with phase := .aliveUninitialized})) == none,
    observed (change projection 4 (fun object => {object with duration := .dynamic})) == none,
    observed (change projection 2 (fun object => {object with type := .record (h "L")})) == none,
    observed (change (projection false true) 4 (fun object => {object with type := .record (h "B")})) == none,
    observed {projection with hierarchy := {hierarchy with root := h "L"}} == none,
    observed {projection with hierarchy := {hierarchy with classes := hierarchy.classes ++ [hierarchy.classes.head!]}} == none,
    observed {projection with hierarchy := {hierarchy with classes := hierarchy.classes ++ [⟨h "unused", false, [], []⟩]}} == none,
    observed {projection with hierarchy := {hierarchy with classes := (
      hierarchy.classes.modify 0 (fun shape => {shape with isAbstract := true}))}} == none,
    observed {projection with hierarchy := {hierarchy with classes := (
      hierarchy.classes.modify 3 (fun shape => {shape with bases := [h "D"]}))}} == none,
    observed {projection with hierarchy := {hierarchy with classes := (
      hierarchy.classes.modify 3 (fun shape => {shape with fields := []}))}} == none,
    observed projection {getter with isConst := false} == some (-9),
    observed (projection false true) {getter with isConst := false} == none
    ].all id = true := by decide

#print axioms kernelSubobjects
#print axioms ClassReceiverProjection.invoke_memory
#print axioms ClassReceiverProjection.invoke_of_check

end LeanModels.Cpp.ClassSubobjectTests
