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

private def declarationRow (id kind canonical : String) : DeclarationEvidenceRow := {
  ordinal := 0, id := h id, kind, canonical := h canonical,
  previous := none, semanticContext := none, lexicalContext := none,
  implicit := false, dependentContext := false, owningModule := none,
  functionShape := none, raw := .object [("name", .string "read")]}

private def declarationRowNamed (id kind canonical name : String) : DeclarationEvidenceRow :=
  {declarationRow id kind canonical with raw := .object [("name", .string name)]}

private def probe (rows : List DeclarationEvidenceRow) : DeclarationProbe :=
  {ast := .object [], metadata := .object [], declarations := rows}

private def canonicalProbe : DeclarationProbe :=
  probe [declarationRow methodHandle.value "CXXMethodDecl" "0xc0",
    declarationRow "0xc0" "CXXMethodDecl" "0xc0"]

private def canonicalGetter : IntegralMemberGetter :=
  {getter with canonical := h "0xc0"}

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

private def rawRefType (id type : String) : Raw := rawObject [
  ("kind", rawText "DeclRefExpr"),
  ("type", rawObject [("qualType", rawText type)]),
  ("referencedDecl", rawObject [("id", rawText id)])]

private def rawRefCast (id : String) : Raw := rawObject [
  ("kind", rawText "ImplicitCastExpr"),
  ("castKind", rawText "LValueToRValue"),
  ("type", rawObject [("qualType", rawText "Owner *")]),
  ("inner", .array [rawRef id])]

private def rawRefNoType (id : String) : Raw := rawObject [
  ("kind", rawText "DeclRefExpr"),
  ("referencedDecl", rawObject [("id", rawText id)])]

private def rawMember (methodId receiverId name : String) : Raw := rawObject [
  ("kind", rawText "MemberExpr"),
  ("isArrow", .bool true),
  ("valueCategory", rawText "prvalue"),
  ("name", rawText name),
  ("referencedMemberDecl", rawObject [("kind", rawText "CXXMethodDecl"), ("id", rawText methodId)]),
  ("inner", .array [rawRef receiverId])]

private def rawMemberDot (methodId receiverId name : String) : Raw := rawObject [
  ("kind", rawText "MemberExpr"),
  ("isArrow", .bool false),
  ("valueCategory", rawText "prvalue"),
  ("name", rawText name),
  ("referencedMemberDecl", rawObject [("kind", rawText "CXXMethodDecl"), ("id", rawText methodId)]),
  ("inner", .array [rawRefType receiverId "Owner"])]

private def rawMemberString (methodId receiverId name : String) : Raw := rawObject [
  ("kind", rawText "MemberExpr"),
  ("isArrow", .bool true),
  ("valueCategory", rawText "prvalue"),
  ("name", rawText name),
  ("referencedMemberDecl", rawText methodId),
  ("inner", .array [rawRef receiverId])]

private def rawMemberCast (methodId receiverId name : String) : Raw := rawObject [
  ("kind", rawText "MemberExpr"),
  ("isArrow", .bool true),
  ("valueCategory", rawText "prvalue"),
  ("name", rawText name),
  ("referencedMemberDecl", rawObject [("kind", rawText "CXXMethodDecl"), ("id", rawText methodId)]),
  ("inner", .array [rawRefCast receiverId])]

private def rawMemberNoType (methodId receiverId name : String) : Raw := rawObject [
  ("kind", rawText "MemberExpr"),
  ("isArrow", .bool true),
  ("valueCategory", rawText "prvalue"),
  ("name", rawText name),
  ("referencedMemberDecl", rawObject [("kind", rawText "CXXMethodDecl"), ("id", rawText methodId)]),
  ("inner", .array [rawRefNoType receiverId])]

private def rawMemberWrongKind (methodId receiverId name : String) : Raw := rawObject [
  ("kind", rawText "MemberExpr"),
  ("isArrow", .bool true),
  ("valueCategory", rawText "prvalue"),
  ("name", rawText name),
  ("referencedMemberDecl", rawObject [
    ("kind", rawText "FieldDecl"), ("id", rawText methodId)]),
  ("inner", .array [rawRef receiverId])]

private def rawCallWithResult (methodId receiverId name result : String) : Raw := rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("type", rawObject [("qualType", rawText result)]),
  ("inner", .array [rawMember methodId receiverId name])]

private def rawCall (methodId receiverId name : String) : Raw :=
  rawCallWithResult methodId receiverId name "int"

private def rawCallDotWithResult (methodId receiverId name result : String) : Raw := rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("type", rawObject [("qualType", rawText result)]),
  ("inner", .array [rawMemberDot methodId receiverId name])]

private def rawCallDot (methodId receiverId name : String) : Raw :=
  rawCallDotWithResult methodId receiverId name "int"

private def rawCallString (methodId receiverId name : String) : Raw := rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("type", rawObject [("qualType", rawText "int")]),
  ("inner", .array [rawMemberString methodId receiverId name])]

private def rawCallCast (methodId receiverId name : String) : Raw := rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("type", rawObject [("qualType", rawText "int")]),
  ("inner", .array [rawMemberCast methodId receiverId name])]

private def rawCallThis (methodId name : String) : Raw := rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("type", rawObject [("qualType", rawText "int")]),
  ("inner", .array [rawObject [
    ("kind", rawText "MemberExpr"), ("isArrow", .bool true),
    ("valueCategory", rawText "prvalue"), ("name", rawText name),
    ("referencedMemberDecl", rawObject [
      ("kind", rawText "CXXMethodDecl"), ("id", rawText methodId)]),
    ("inner", .array [rawObject [
      ("kind", rawText "CXXThisExpr"),
      ("type", rawObject [("qualType", rawText "Owner *")])]])]])]

private def syntaxError (raw : Raw) : Option IntegralMemberCallSyntaxError :=
  match IntegralMemberCallSyntax.admit raw with
  | .error reason => some reason
  | .ok _ => none

private def observed (raw : Raw) : Option Int :=
  match IntegralMemberCallSyntax.admit raw with
  | .error _ => none
  | .ok evidence =>
      match IntegralMemberCall.bind evidence getter receiverHandle projection with
      | .error _ => none
      | .ok call =>
          match call.invoke with
          | .ok (memory, value) =>
              if memory == projection.snapshot.memory then some value.value else none
          | .error _ => none

private def observedDot : Option Int :=
  observed (rawCallDot methodHandle.value receiverHandle.value "read")

private def observedString : Option Int :=
  observed (rawCallString methodHandle.value receiverHandle.value "read")

private def observedCast : Option Int :=
  observed (rawCallCast methodHandle.value receiverHandle.value "read")

private def bindingError (raw : Raw) : Option IntegralMemberCallError :=
  match IntegralMemberCallSyntax.admit raw with
  | .error _ => none
  | .ok evidence =>
      match IntegralMemberCall.bind evidence getter receiverHandle projection with
      | .error reason => some reason
      | .ok _ => none

private def bindingTypeError (raw : Raw) : Option IntegralMemberCallError :=
  match IntegralMemberCallSyntax.admit raw with
  | .error _ => none
  | .ok evidence =>
      let other := {projection with hierarchy := {hierarchy with classes :=
        (hierarchy.classes.modify 0 (fun shape => {shape with name := "Other"}))}}
      match IntegralMemberCall.bind evidence getter receiverHandle other with
      | .error reason => some reason
      | .ok _ => none

private def bindingResultError (raw : Raw) : Option IntegralMemberCallError :=
  match IntegralMemberCallSyntax.admit raw with
  | .error _ => none
  | .ok evidence =>
      match IntegralMemberCall.bind evidence getter receiverHandle projection with
      | .error reason => some reason
      | .ok _ => none

#guard (IntegralMemberCallSyntax.admit (rawCall methodHandle.value receiverHandle.value "read")).isOk
#guard observed (rawCall methodHandle.value receiverHandle.value "read") == some 7
#guard (IntegralMemberCallSyntax.admit (rawCallDot methodHandle.value receiverHandle.value "read")).isOk
#guard observedDot == some 7
#guard (IntegralMemberCallSyntax.admit (rawCallString methodHandle.value receiverHandle.value "read")).isOk
#guard observedString == some 7
#guard (IntegralMemberCallSyntax.admit (rawCallCast methodHandle.value receiverHandle.value "read")).isOk
#guard observedCast == some 7
#guard syntaxError (rawCallThis methodHandle.value "read") == some .missingThisOwner

private def resolveCanonicalHandle (rows : List DeclarationEvidenceRow) : Option FrontendHandle :=
  match IntegralMemberCallSyntax.admit (rawCall methodHandle.value receiverHandle.value "read") with
  | .error _ => none
  | .ok evidence =>
      match IntegralMemberCallSyntax.resolveCanonical (probe rows) evidence with
      | .error _ => none
      | .ok resolved => some resolved.canonicalMethod

private def resolveCanonicalError (rows : List DeclarationEvidenceRow) :
    Option IntegralMemberCallSyntaxError :=
  match IntegralMemberCallSyntax.admit (rawCall methodHandle.value receiverHandle.value "read") with
  | .error reason => some reason
  | .ok evidence =>
      match IntegralMemberCallSyntax.resolveCanonical (probe rows) evidence with
      | .error reason => some reason
      | .ok _ => none

private def observedCanonical : Option Int :=
  match IntegralMemberCallSyntax.admit (rawCall methodHandle.value receiverHandle.value "read") with
  | .error _ => none
  | .ok evidence =>
      match IntegralMemberCallSyntax.resolveCanonical canonicalProbe evidence with
      | .error _ => none
      | .ok resolved =>
          match IntegralMemberCall.bind resolved canonicalGetter receiverHandle projection with
          | .error _ => none
          | .ok call =>
              match call.invoke with
              | .ok (memory, value) =>
                  if memory == projection.snapshot.memory then some value.value else none
              | .error _ => none

private def bindingCanonicalError : Option IntegralMemberCallError :=
  match IntegralMemberCallSyntax.admit (rawCall methodHandle.value receiverHandle.value "read") with
  | .error _ => none
  | .ok evidence =>
      match IntegralMemberCall.bind evidence canonicalGetter receiverHandle projection with
      | .error reason => some reason
      | .ok _ => none

private def resolvedCanonicalHandle (rows : List DeclarationEvidenceRow) :
    Option FrontendHandle :=
  match IntegralMemberCallSyntax.admitResolved (probe rows)
      (rawCall methodHandle.value receiverHandle.value "read") with
  | .error _ => none
  | .ok evidence => some evidence.canonicalMethod

#guard resolveCanonicalHandle [declarationRow methodHandle.value "CXXMethodDecl" "0xc0",
    declarationRow "0xc0" "CXXMethodDecl" "0xc0"] == some (h "0xc0")
#guard resolveCanonicalHandle [declarationRow methodHandle.value "CXXMethodDecl" "0xc0",
    declarationRow methodHandle.value "CXXMethodDecl" "0xc0",
    declarationRow "0xc0" "CXXMethodDecl" "0xc0"] == some (h "0xc0")
#guard resolveCanonicalError [] == some .canonicalMethodMissing
#guard resolveCanonicalError [declarationRow methodHandle.value "FieldDecl" "0xc0"] ==
  some .canonicalMethodMissing
#guard resolveCanonicalError [declarationRow methodHandle.value "CXXMethodDecl" "0xc0"] ==
  some .canonicalMethodTargetMissing
#guard resolveCanonicalError [declarationRow methodHandle.value "CXXMethodDecl" "0xc0",
    declarationRowNamed "0xc0" "CXXMethodDecl" "0xc0" "write"] ==
  some .canonicalMethodTargetMismatch
#guard resolveCanonicalError [declarationRow methodHandle.value "CXXMethodDecl" "0xc0",
    declarationRow methodHandle.value "CXXMethodDecl" "0xc1"] == some .canonicalMethodAmbiguous
#guard observedCanonical == some 7
#guard bindingCanonicalError == some .canonicalMethodMismatch
#guard resolvedCanonicalHandle canonicalProbe.declarations == some (h "0xc0")

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
    ("kind", rawText "MemberExpr"), ("isArrow", .bool true),
    ("valueCategory", rawText "prvalue"), ("name", rawText "read"),
    ("referencedMemberDecl", rawObject [
      ("kind", rawText "CXXMethodDecl"), ("id", rawText methodHandle.value)]),
    ("inner", .array [rawObject [("kind", rawText "IntegerLiteral")]])]])]) ==
  some .unsupportedReceiver
#guard syntaxError (rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("inner", .array [rawObject [
    ("kind", rawText "MemberExpr"), ("isArrow", .bool true),
    ("valueCategory", rawText "prvalue"), ("name", rawText "read"),
    ("inner", .array [rawRef receiverHandle.value])]])]) == some .missingMethodHandle
#guard syntaxError (rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("inner", .array [rawMemberNoType methodHandle.value receiverHandle.value "read"])]) ==
    some .malformedReceiverType
#guard syntaxError (rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("inner", .array [rawMember methodHandle.value receiverHandle.value "read"])]) ==
    some .malformedResultType
#guard syntaxError (rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("inner", .array [rawMember methodHandle.value receiverHandle.value "bad-name"])]) ==
    some .malformedName
#guard syntaxError (rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("inner", .array [rawMemberWrongKind methodHandle.value receiverHandle.value "read"])]) ==
    some .unsupportedMethod
#guard bindingError (rawCall "0xf" receiverHandle.value "read") == some .methodMismatch
#guard bindingError (rawCall methodHandle.value receiverHandle.value "other") == some .nameMismatch
#guard bindingError (rawCall methodHandle.value "0xe" "read") == some .receiverMismatch
#guard bindingTypeError (rawCall methodHandle.value receiverHandle.value "read") ==
  some .receiverTypeMismatch
#guard bindingResultError (rawCallWithResult methodHandle.value receiverHandle.value "read" "long") ==
  some .resultTypeMismatch

end LeanModels.Cpp.MemberCallTests
