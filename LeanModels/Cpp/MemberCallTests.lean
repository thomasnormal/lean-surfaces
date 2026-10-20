import LeanModels.Cpp.MemberCalls

namespace LeanModels.Cpp.MemberCallTests

private def h (value : String) : FrontendHandle := ⟨value⟩
private def ownerHandle : FrontendHandle := h "0xa"
private def fieldHandle : FrontendHandle := h "0xb"
private def methodHandle : FrontendHandle := h "0xc"
private def receiverHandle : FrontendHandle := h "0xd"

private def hierarchy : ClassHierarchy := {
  root := ownerHandle,
  classes := [{declaration := ownerHandle, isAbstract := false, bases := [], fields := [fieldHandle], friends := [], name := "Owner"}]}

private def getter : IntegralMemberGetter := {
  occurrence := {(default : Declaration) with id := methodHandle.value, kind := "CXXMethodDecl", name := some "read"},
  owner := ownerHandle,
  field := {declaration := fieldHandle, name := "value", type := .builtin .int, isMutable := false},
  isConst := true, conversions := [], result := .int}

private def projection : ClassReceiverProjection := {
  hierarchy, objects := [0], receiverPath := [],
  snapshot := {
  memory := {
      profile := .lp64,
      objects := {objects := [
        {duration := .automatic, type := .record ownerHandle, phase := .aliveInitialized},
        {duration := .automatic, type := .builtin .int, phase := .aliveInitialized}]},
      values := [none, some ⟨.signed 32, 7⟩]},
    object := 0, member := 1, field := fieldHandle}}

private def rawObject (fields : List (String × Raw)) : Raw := .object fields
private def rawText (value : String) : Raw := .string value

private def rawRef (id : String) : Raw := rawObject [
  ("kind", rawText "DeclRefExpr"),
  ("type", rawObject [("qualType", rawText "Owner *")]),
  ("referencedDecl", rawObject [("id", rawText id)])]

private def rawRefNoType (id : String) : Raw := rawObject [
  ("kind", rawText "DeclRefExpr"),
  ("referencedDecl", rawObject [("id", rawText id)])]

private def rawMember (methodId receiverId name : String) : Raw := rawObject [
  ("kind", rawText "MemberExpr"),
  ("isArrow", .bool true),
  ("valueCategory", rawText "lvalue"),
  ("name", rawText name),
  ("referencedMemberDecl", rawObject [("id", rawText methodId)]),
  ("inner", .array [rawRef receiverId])]

private def rawMemberNoType (methodId receiverId name : String) : Raw := rawObject [
  ("kind", rawText "MemberExpr"),
  ("isArrow", .bool true),
  ("valueCategory", rawText "lvalue"),
  ("name", rawText name),
  ("referencedMemberDecl", rawObject [("id", rawText methodId)]),
  ("inner", .array [rawRefNoType receiverId])]

private def rawCall (methodId receiverId name : String) : Raw := rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("inner", .array [rawMember methodId receiverId name])]

private def syntaxError (raw : Raw) : Option IntegralMemberCallSyntaxError :=
  match IntegralMemberCallSyntax.admit raw with
  | .error reason => some reason
  | .ok _ => none

private def observed (raw : Raw) : Option Int :=
  match IntegralMemberCallSyntax.admit raw with
  | .error _ => none
  | .ok evidence =>
      match IntegralMemberCall.bind evidence getter receiverHandle "Owner *" projection with
      | .error _ => none
      | .ok call =>
          match call.invoke with
          | .ok (memory, value) =>
              if memory == projection.snapshot.memory then some value.value else none
          | .error _ => none

private def bindingError (raw : Raw) : Option IntegralMemberCallError :=
  match IntegralMemberCallSyntax.admit raw with
  | .error _ => none
  | .ok evidence =>
      match IntegralMemberCall.bind evidence getter receiverHandle "Owner *" projection with
      | .error reason => some reason
      | .ok _ => none

private def bindingTypeError (raw : Raw) (receiverType : String) :
    Option IntegralMemberCallError :=
  match IntegralMemberCallSyntax.admit raw with
  | .error _ => none
  | .ok evidence =>
      match IntegralMemberCall.bind evidence getter receiverHandle receiverType projection with
      | .error reason => some reason
      | .ok _ => none

#guard (IntegralMemberCallSyntax.admit (rawCall methodHandle.value receiverHandle.value "read")).isOk
#guard observed (rawCall methodHandle.value receiverHandle.value "read") == some 7
#guard syntaxError (rawObject []) == some .notMemberCall
#guard syntaxError (rawObject [
  ("kind", rawText "CXXMemberCallExpr"), ("inner", .array [])]) ==
    some .malformedChildren
#guard syntaxError (rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("inner", .array [rawMember methodHandle.value receiverHandle.value "read", rawRef "0xe"])]) ==
    some .unsupportedArguments
#guard syntaxError (rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("inner", .array [rawObject [
    ("kind", rawText "MemberExpr"), ("isArrow", .bool false),
    ("valueCategory", rawText "lvalue"), ("name", rawText "read"),
    ("referencedMemberDecl", rawObject [("id", rawText methodHandle.value)]),
    ("inner", .array [rawRef receiverHandle.value])]])]) == some .unsupportedReceiver
#guard syntaxError (rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("inner", .array [rawObject [
    ("kind", rawText "MemberExpr"), ("isArrow", .bool true),
    ("valueCategory", rawText "lvalue"), ("name", rawText "read"),
    ("inner", .array [rawRef receiverHandle.value])]])]) == some .missingMethodHandle
#guard syntaxError (rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("inner", .array [rawMemberNoType methodHandle.value receiverHandle.value "read"])]) ==
    some .malformedReceiverType
#guard syntaxError (rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("inner", .array [rawMember methodHandle.value receiverHandle.value "bad-name"])]) ==
    some .malformedName
#guard bindingError (rawCall "0xf" receiverHandle.value "read") == some .methodMismatch
#guard bindingError (rawCall methodHandle.value receiverHandle.value "other") == some .nameMismatch
#guard bindingError (rawCall methodHandle.value "0xe" "read") == some .receiverMismatch
#guard bindingTypeError (rawCall methodHandle.value receiverHandle.value "read") "Other *" ==
  some .receiverTypeMismatch

end LeanModels.Cpp.MemberCallTests
