import LeanModels.Cpp.ClassBaseViews

namespace LeanModels.Cpp.ClassBaseViewTests

private def h (name : String) : FrontendHandle := ⟨name⟩
private def b (name access : String := "public") : ClassBaseSpec :=
  {target := h name, access, writtenAccess := access}
private def hierarchy : ClassHierarchy := {
  root := h "D", classes := [
    ⟨h "D", false, [b "L", b "R"], [], []⟩,
    ⟨h "L", true, [b "B"], [], []⟩,
    ⟨h "R", true, [b "B"], [], []⟩,
    ⟨h "B", true, [], [], []⟩]}

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

private def castOn (candidate : ClassBaseView) (source target : String) : ClassBaseCast :=
  {view := candidate, sourceDeclaration := h source, targetDeclaration := h target}

private def observedCast (candidate : ClassBaseCast) : Option ObjectId :=
  match candidate.execute with
  | .ok (returned, object) => if returned == candidate.view.memory then some object else none
  | _ => none

private def rawText (value : String) : Raw := .string value
private def rawObject (fields : List (String × Raw)) : Raw := .object fields

private def rawType (qualType : String) : Raw :=
  rawObject [("qualType", rawText qualType)]

private def rawDeclRef (qualType : String) : Raw :=
  rawObject [
    ("kind", rawText "DeclRefExpr"),
    ("type", rawType qualType)]

private def rawLValue (qualType : String) (operand : Raw) : Raw :=
  rawObject [
    ("kind", rawText "ImplicitCastExpr"),
    ("castKind", rawText "LValueToRValue"),
    ("type", rawType qualType),
    ("inner", .array [operand])]

private def rawDerivedToBase (targetType : String) (sourceType : String) : Raw :=
  rawObject [
    ("kind", rawText "ImplicitCastExpr"),
    ("castKind", rawText "DerivedToBase"),
    ("type", rawType targetType),
    ("path", .array [rawObject [("name", rawText "B")]]),
    ("inner", .array [rawLValue sourceType (rawDeclRef sourceType)])]

private def rawBaseCast (sourceType targetType : String) : Raw :=
  rawObject [
    ("kind", rawText "CXXStaticCastExpr"),
    ("castKind", rawText "NoOp"),
    ("type", rawType targetType),
    ("inner", .array [rawDerivedToBase targetType sourceType])]

private def syntaxError (raw : Raw) (sourceType targetType : String) :
    Option ClassBaseCastSyntaxError :=
  match ClassBaseCastSyntax.admit raw sourceType targetType with
  | .ok _ => none
  | .error reason => some reason

private def observedAdmittedCast (raw : Raw) : Option ObjectId :=
  match ClassBaseCastSyntax.admit raw "D *" "L *" with
  | .error _ => none
  | .ok admitted =>
      observedCast (ClassBaseCastSyntax.bind admitted (castOn (view [] [0]) "D" "L"))

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
            {shape with bases := [b "L" "private", b "R"], friends := [h "F"]}))} [] [0] "F") == some 1,
      observed (contextualOn {hierarchy with classes :=
          (hierarchy.classes.modify 0 (fun shape =>
            {shape with bases := [b "L" "private", b "R"], friends := [h "friend_fn"]}))} [] [0]
          "friend_fn") == some 1,
      observed (contextualOn {hierarchy with classes :=
          (hierarchy.classes.modify 0 (fun shape =>
            {shape with bases := [b "L" "protected", b "R"]}))} [] [0] "D") == some 1,
      observed (contextualOn {hierarchy with classes :=
          (hierarchy.classes.modify 0 (fun shape =>
            {shape with bases := [b "L" "protected", b "R"], friends := [h "F"]}))} [] [0] "F") == some 1,
      observed (contextualOn {hierarchy with classes :=
          (hierarchy.classes.modify 0 (fun shape =>
            {shape with bases := [b "L" "protected", b "R"]}))} [] [0] "R") == none,
      observed (contextualOn {hierarchy with classes :=
          (hierarchy.classes.modify 1 (fun shape =>
            {shape with bases := [b "B" "protected"]}))} [] [0, 0] "D") == some 2,
      observedCast (castOn (view [] [0]) "D" "L") == some 1,
      observedCast (castOn (view [] [0]) "L" "L") == none,
      observedCast (castOn (view [] [0]) "D" "B") == none,
      observedCast (castOn {view [] [0] with hierarchy := {hierarchy with classes :=
        (hierarchy.classes.modify 0 (fun shape =>
          {shape with bases := [b "L" "private", b "R"]}))}} "D" "L") == none,
      observedCast (castOn (contextualOn {hierarchy with classes :=
        (hierarchy.classes.modify 0 (fun shape =>
          {shape with bases := [b "L" "private", b "R"], friends := [h "F"]}))} [] [0] "F") "D" "L") == some 1
    ].all id = true := by decide

set_option maxRecDepth 10000 in
private theorem kernelCastSyntax :
    [
      (ClassBaseCastSyntax.admit (rawBaseCast "D *" "L *") "D *" "L *").isOk,
      (ClassBaseCastSyntax.admit (rawBaseCast "D *" "L *") "D *" "L *").toOption ==
        some {sourceType := "D *", targetType := "L *"},
      observedAdmittedCast (rawBaseCast "D *" "L *") == some 1,
      syntaxError (rawBaseCast "D *" "L *") "D *" "L *" == none,
      syntaxError (rawBaseCast "D *" "L *") "L *" "L *" == some .malformedType,
      syntaxError (rawObject [("kind", rawText "BinaryOperator")]) "D *" "L *" ==
        some .notStaticCast,
      syntaxError (rawObject [
        ("kind", rawText "CXXStaticCastExpr"),
        ("castKind", rawText "BitCast"),
        ("type", rawType "L *"),
        ("inner", .array [rawDerivedToBase "L *" "D *"])]) "D *" "L *" ==
        some .unsupportedCastKind,
      syntaxError (rawObject [
        ("kind", rawText "CXXStaticCastExpr"),
        ("castKind", rawText "NoOp"),
        ("type", rawType "L *"),
        ("inner", .array [rawObject [
          ("kind", rawText "ImplicitCastExpr"),
          ("castKind", rawText "BaseToDerived"),
          ("type", rawType "L *"),
          ("path", .array [rawObject [("name", rawText "B")]]),
          ("inner", .array [rawLValue "D *" (rawDeclRef "D *")])]])])
        "D *" "L *" == some .unsupportedCastKind,
      syntaxError (rawObject [
        ("kind", rawText "CXXStaticCastExpr"),
        ("castKind", rawText "NoOp"),
        ("type", rawType "L *"),
        ("inner", .array [rawObject [
          ("kind", rawText "ImplicitCastExpr"),
          ("castKind", rawText "DerivedToBase"),
          ("type", rawType "L *"),
          ("path", .array []),
          ("inner", .array [rawLValue "D *" (rawDeclRef "D *")])]])])
        "D *" "L *" == some .missingBasePath,
      syntaxError (rawObject [
        ("kind", rawText "CXXStaticCastExpr"),
        ("castKind", rawText "NoOp"),
        ("type", rawType "L *"),
        ("inner", .array [rawDerivedToBase "L *" "D *"])] )
        "D *" "B *" == some .malformedType,
      syntaxError (rawObject [
        ("kind", rawText "CXXStaticCastExpr"),
        ("castKind", rawText "NoOp"),
        ("type", rawType "L *"),
        ("inner", .array [rawObject [
          ("kind", rawText "ImplicitCastExpr"),
          ("castKind", rawText "DerivedToBase"),
          ("type", rawType "L *"),
          ("path", .array [rawObject [("name", rawText "B")]]),
          ("inner", .array [rawLValue "D *" (rawObject [
            ("kind", rawText "MemberExpr")])])]])])
        "D *" "L *" == some .unsupportedOperand
    ].all id = true := by decide

#print axioms kernelViews
#print axioms ClassBaseView.convert_of_check
#print axioms ClassBaseView.convert_memory
#print axioms ClassBaseCast.execute_memory

end LeanModels.Cpp.ClassBaseViewTests
