import LeanModels.Cpp.MemberCalls

namespace LeanModels.Cpp.MemberCallTests

private def h (value : String) : FrontendHandle := ⟨value⟩
private def ownerHandle : FrontendHandle := h "0xa"
private def fieldHandle : FrontendHandle := h "0xb"
private def methodHandle : FrontendHandle := h "0xc"
private def receiverHandle : FrontendHandle := h "0xd"
private def receiverFieldHandle : FrontendHandle := h "0xe"

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
private def rawNat (value : Nat) : Raw := .number (toString value)

private def rawWithField (raw : Raw) (name : String) (value : Raw) : Raw :=
  match raw with
  | .object fields => .object (fields.map fun entry =>
      if entry.1 == name then (name, value) else entry)
  | _ => raw

private def rawIntegerArgument (id value : String) : Raw := rawObject [
  ("id", rawText id), ("kind", rawText "IntegerLiteral"),
  ("type", rawObject [("qualType", rawText "int")]), ("value", rawText value)]

private def integerArgument : Option IntegralMemberIntegerArgument :=
  (IntegralMemberIntegerArgument.admit (rawIntegerArgument "0xf" "0")).toOption

private def boundIntegerArgument : Option IntegralMemberBoundIntegerArgument := do
  let argument ← integerArgument
  IntegralMemberIntegerArgument.bind argument (h "0x10") (.builtin .int) |>.toOption

private def parameterRaw : Raw := rawObject [
  ("kind", rawText "CXXMethodDecl"), ("id", rawText methodHandle.value),
  ("method_parameter_types", .array [rawObject [
    ("kind", rawText "builtin"), ("name", rawText "int")]])]

private def parameterAst : Raw := rawObject [
  ("kind", rawText "CXXMethodDecl"), ("id", rawText methodHandle.value),
  ("inner", .array [rawObject [
    ("kind", rawText "ParmVarDecl"), ("id", rawText "0x10"),
    ("name", rawText "flags"),
    ("type", rawObject [("qualType", rawText "int")])]])]

private def parameterProbe : DeclarationProbe :=
  {ast := parameterAst, metadata := .object [],
    declarations := [declarationRow methodHandle.value "CXXMethodDecl" methodHandle.value]
      |>.map fun row => {row with raw := parameterRaw}}

private def profileRaw : Raw := rawObject [
  ("kind", rawText "CXXMethodDecl"), ("id", rawText methodHandle.value),
  ("method_shape_api", rawText "CXXMethodDecl receiver shape v1"),
  ("method_signature_api", rawText "FunctionDecl return and parameter projection v1"),
  ("definition", .bool true), ("body_present", .bool true),
  ("defaulted", .bool false), ("deleted_as_written", .bool false),
  ("function_has_skipped_body", .bool false),
  ("function_will_have_body", .bool false),
  ("function_has_defining_attr", .bool false),
  ("function_late_template_parsed", .bool false),
  ("function_explicitly_defaulted", .bool false),
  ("function_attribute_count", rawNat 0),
  ("own_body_kind", rawText "CompoundStmt"),
  ("own_body_owner", rawText methodHandle.value),
  ("method_const", .bool false), ("method_static", .bool false),
  ("method_volatile", .bool false), ("method_virtual", .bool false),
  ("method_pure", .bool false), ("method_variadic", .bool false),
  ("method_exception_spec", rawNat 0), ("method_ref_qualifier", rawNat 0),
  ("method_parameter_types", .array [rawObject [
    ("kind", rawText "builtin"), ("name", rawText "int")]]),
  ("method_result_type", rawObject [("kind", rawText "builtin"),
    ("name", rawText "void")])]

private def profileProbe : DeclarationProbe :=
  {ast := parameterAst, metadata := .object [],
    declarations := [declarationRow methodHandle.value "CXXMethodDecl" methodHandle.value]
      |>.map fun row => {row with raw := profileRaw}}

private def methodProfile : Option IntegralMemberMethodProfile :=
  (IntegralMemberMethodProfile.admit profileProbe methodHandle).toOption

private def canonicalOnlyRaw : Raw := rawObject [
  ("kind", rawText "CXXMethodDecl"), ("id", rawText methodHandle.value),
  ("definition", .bool false)]

private def definitionRaw : Raw :=
  rawWithField (rawWithField profileRaw "id" (rawText "0x11"))
    "own_body_owner" (rawText "0x11")

private def definitionProbe : DeclarationProbe :=
  {ast := rawWithField parameterAst "id" (rawText "0x11"), metadata := .object [],
    declarations := [
      {declarationRow methodHandle.value "CXXMethodDecl" methodHandle.value with
        raw := canonicalOnlyRaw},
      {declarationRow "0x11" "CXXMethodDecl" methodHandle.value with raw := definitionRaw}]}

private def methodBody : Option IntegralMemberMethodBody :=
  (IntegralMemberMethodBody.admit definitionProbe methodHandle).toOption

private def parameterEvidence : Option IntegralMemberParameterEvidence :=
  (IntegralMemberIntegerArgument.parameter parameterProbe methodHandle 0).toOption

private def boundWitnessedIntegerArgument : Option IntegralMemberBoundIntegerArgument := do
  let argument ← integerArgument
  let parameter ← parameterEvidence
  IntegralMemberIntegerArgument.bindTo argument parameter |>.toOption

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

private def rawRefCastNoOp (id : String) : Raw := rawObject [
  ("kind", rawText "ImplicitCastExpr"),
  ("castKind", rawText "NoOp"),
  ("type", rawObject [("qualType", rawText "Owner *")]),
  ("inner", .array [rawRefCast id])]

private def rawFieldRefCast (id : String) : Raw := rawObject [
  ("kind", rawText "ImplicitCastExpr"),
  ("castKind", rawText "LValueToRValue"),
  ("type", rawObject [("qualType", rawText "Owner *")]),
  ("inner", .array [rawRefType id "Owner *"])]

private def rawRefDerived (id : String) : Raw := rawObject [
  ("kind", rawText "ImplicitCastExpr"),
  ("castKind", rawText "UncheckedDerivedToBase"),
  ("type", rawObject [("qualType", rawText "Owner *")]),
  ("path", .array [rawObject [("name", rawText "Base")]]),
  ("inner", .array [rawRefType id "Derived *"])]

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

private def rawCallCastNoOp (methodId receiverId name : String) : Raw := rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("type", rawObject [("qualType", rawText "int")]),
  ("inner", .array [rawObject [
    ("kind", rawText "MemberExpr"), ("isArrow", .bool true),
    ("valueCategory", rawText "prvalue"), ("name", rawText name),
    ("referencedMemberDecl", rawObject [
      ("kind", rawText "CXXMethodDecl"), ("id", rawText methodId)]),
    ("inner", .array [rawRefCastNoOp receiverId])]])]

private def rawCallDerived (methodId receiverId name : String) : Raw := rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("type", rawObject [("qualType", rawText "int")]),
  ("inner", .array [rawObject [
    ("kind", rawText "MemberExpr"), ("isArrow", .bool true),
    ("valueCategory", rawText "prvalue"), ("name", rawText name),
    ("referencedMemberDecl", rawObject [
      ("kind", rawText "CXXMethodDecl"), ("id", rawText methodId)]),
    ("inner", .array [rawRefDerived receiverId])]])]

private def rawNestedField (fieldId receiverId : String) : Raw := rawObject [
  ("kind", rawText "MemberExpr"),
  ("isArrow", .bool true),
  ("valueCategory", rawText "lvalue"),
  ("name", rawText "pool"),
  ("type", rawObject [("qualType", rawText "MemPool *")]),
  ("referencedMemberDecl", rawObject [
    ("kind", rawText "FieldDecl"), ("id", rawText fieldId)]),
  ("inner", .array [rawFieldRefCast receiverId])]

private def rawNestedMember (methodId fieldId receiverId name : String) : Raw := rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("type", rawObject [("qualType", rawText "int")]),
  ("inner", .array [rawObject [
    ("kind", rawText "MemberExpr"), ("isArrow", .bool true),
    ("valueCategory", rawText "prvalue"), ("name", rawText name),
    ("referencedMemberDecl", rawObject [
      ("kind", rawText "CXXMethodDecl"), ("id", rawText methodId)]),
    ("inner", .array [rawObject [
      ("kind", rawText "ImplicitCastExpr"),
      ("castKind", rawText "LValueToRValue"),
      ("type", rawObject [("qualType", rawText "MemPool *")]),
      ("inner", .array [rawNestedField fieldId receiverId])]])]])]

private def rawNestedCall (methodId innerMethodId receiverId name : String) : Raw := rawObject [
  ("kind", rawText "CXXMemberCallExpr"),
  ("type", rawObject [("qualType", rawText "int")]),
  ("inner", .array [rawObject [
    ("kind", rawText "MemberExpr"), ("isArrow", .bool true),
    ("valueCategory", rawText "prvalue"), ("name", rawText name),
    ("referencedMemberDecl", rawObject [
      ("kind", rawText "CXXMethodDecl"), ("id", rawText methodId)]),
    ("inner", .array [rawCallDerived innerMethodId receiverId "Parent"])]])]

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

private def observedCastNoOp : Option Int :=
  observed (rawCallCastNoOp methodHandle.value receiverHandle.value "read")

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
#guard (IntegralMemberCallSyntax.admit (rawCallCastNoOp methodHandle.value receiverHandle.value "read")).isOk
#guard observedCastNoOp == some 7
#guard (IntegralMemberCallSyntax.admit (rawCallDerived methodHandle.value receiverHandle.value "read")).isOk
#guard (IntegralMemberCallSyntax.admit (rawCallDerived methodHandle.value receiverHandle.value "read")).toOption.map
    (fun evidence => evidence.receiverCast) == some ["UncheckedDerivedToBase[Base]"]
#guard (IntegralMemberCallSyntax.admit
    (rawNestedMember methodHandle.value receiverFieldHandle.value receiverHandle.value "read")).isOk
#guard (IntegralMemberCallSyntax.admit
    (rawNestedMember methodHandle.value receiverFieldHandle.value receiverHandle.value "read")).toOption.map
    (fun evidence => (evidence.receiver, evidence.receiverField, evidence.receiverBase,
      evidence.receiverFieldName, evidence.receiverCast)) ==
    some (receiverFieldHandle, some receiverFieldHandle, some receiverHandle,
      some "pool", ["LValueToRValue", "LValueToRValue"])
#guard integerArgument.map (fun argument =>
    (argument.occurrence, argument.sourceType, argument.type, argument.value)) ==
    some (h "0xf", "int", .builtin .int, 0)
#guard boundIntegerArgument.map (fun bound =>
    (bound.parameter, bound.parameterType, bound.argument.value)) ==
    some (h "0x10", .builtin .int, 0)
#guard parameterEvidence.map (fun parameter =>
    (parameter.method, parameter.parameter, parameter.ordinal, parameter.name,
      parameter.sourceType, parameter.type)) ==
    some (methodHandle, h "0x10", 0, some "flags", "int", .builtin .int)
#guard methodProfile.map (fun profile =>
    (profile.method, profile.resultType, profile.parameters, profile.isConst,
      profile.isStatic, profile.bodyKind)) ==
    some (methodHandle, .void, [.builtin .int], false, false, "CompoundStmt")
#guard methodBody.map (fun body =>
    (body.canonical, body.definition, body.bodyKind)) ==
    some (methodHandle, h "0x11", "CompoundStmt")
#guard boundWitnessedIntegerArgument.map (fun bound =>
    (bound.parameter, bound.parameterType, bound.argument.value)) ==
    some (h "0x10", .builtin .int, 0)
#guard (IntegralMemberIntegerArgument.admit
    (rawObject [("kind", rawText "CharacterLiteral")])).toOption.isNone
#guard (IntegralMemberIntegerArgument.admit
    (rawObject [("kind", rawText "IntegerLiteral"),
      ("id", rawText "0xf"), ("type", rawObject [("qualType", rawText "long")]),
      ("value", rawText "0")])).toOption.isNone
#guard integerArgument.map (fun argument =>
    IntegralMemberIntegerArgument.bind argument (h "0x10") (.builtin .long)) matches .some (.error .parameterTypeMismatch)
#guard syntaxError (rawNestedCall methodHandle.value methodHandle.value receiverHandle.value "read") ==
  some .unsupportedReceiver
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
