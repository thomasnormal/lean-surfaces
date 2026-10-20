import LeanModels.Cpp.ClassBaseViews

namespace LeanModels.Cpp.ClassBaseViewTests

private def h (name : String) : FrontendHandle := ⟨name⟩
private def b (name access : String := "public") : ClassBaseSpec :=
  {target := h name, access, writtenAccess := access}
private def hierarchy : ClassHierarchy := {
  root := h "D", classes := [
    ⟨h "D", false, [b "L", b "R"], []⟩,
    ⟨h "L", true, [b "B"], []⟩,
    ⟨h "R", true, [b "B"], []⟩,
    ⟨h "B", true, [], []⟩]}

private def memory (constant : Bool := false) : IntegralObjectStore := {
  profile := .lp64,
  objects := {objects := ([h "D", h "L", h "B", h "R", h "B"].map
    (fun name => ⟨.automatic, integralMemberViewType (.record name) constant,
      .aliveInitialized⟩))},
  values := [none, none, none, none, none]}

private def viewOn (hierarchy : ClassHierarchy) (source target : List Nat)
    (constant : Bool := false) : ClassBaseView :=
  {hierarchy, objects := [0, 1, 2, 3, 4], sourcePath := source,
    targetPath := target, memory := memory constant}

private def view (source target : List Nat) (constant : Bool := false) : ClassBaseView :=
  viewOn hierarchy source target constant

private def contextualOn (hierarchy : ClassHierarchy) (source target : List Nat)
    (context : String) : ClassBaseView :=
  {viewOn hierarchy source target with accessContext := some (h context)}

private def observed (candidate : ClassBaseView) : Option ObjectId :=
  match candidate.convert with
  | .ok (returned, object) => if returned == candidate.memory then some object else none
  | _ => none

set_option maxRecDepth 10000 in
private theorem kernelViews :
    [
      observed (view [] [0]) == some 1,
      observed (view [] [1]) == some 3,
      observed (view [0] [0, 0]) == some 2,
      observed (view [1] [1, 0]) == some 4,
      observed (view [] [0, 0]) == some 2,
      observed (view [0] [1, 0]) == none,
      observed (view [0] [0]) == none,
      observed (view [0] [9]) == none,
      observed (view [] [0, 0] true) == some 2,
      observed {view [] [0] with objects := [0, 1, 1, 3, 4]} == none,
      observed {view [] [0] with objects := [0, 1, 2, 3]} == none,
      observed {view [] [0] with memory := {memory with values := [none]}} == none,
      observed {view [] [0] with hierarchy := {hierarchy with classes :=
        (hierarchy.classes.modify 0 (fun shape =>
          {shape with bases := [b "L" "private", b "R"]}))}} == none,
      observed {view [] [0] with hierarchy := {hierarchy with classes :=
        (hierarchy.classes.modify 0 (fun shape =>
          {shape with bases := [b "L" "protected", b "R"]}))}} == none,
      observed (contextualOn {hierarchy with classes :=
          (hierarchy.classes.modify 0 (fun shape =>
            {shape with bases := [b "L" "private", b "R"]}))} [] [0] "D") == some 1,
      observed (contextualOn {hierarchy with classes :=
          (hierarchy.classes.modify 0 (fun shape =>
            {shape with bases := [b "L" "private", b "R"]}))} [] [0] "L") == none,
      observed (contextualOn {hierarchy with classes :=
          (hierarchy.classes.modify 0 (fun shape =>
            {shape with bases := [b "L" "protected", b "R"]}))} [] [0] "D") == some 1,
      observed (contextualOn {hierarchy with classes :=
          (hierarchy.classes.modify 0 (fun shape =>
            {shape with bases := [b "L" "protected", b "R"]}))} [] [0] "R") == none,
      observed (contextualOn {hierarchy with classes :=
          (hierarchy.classes.modify 1 (fun shape =>
            {shape with bases := [b "B" "protected"]}))} [] [0, 0] "D") == some 2
    ].all id = true := by decide

#print axioms kernelViews
#print axioms ClassBaseView.convert_of_check
#print axioms ClassBaseView.convert_memory

end LeanModels.Cpp.ClassBaseViewTests
