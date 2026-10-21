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

private def rawWithFieldOrAppend (raw : Raw) (name : String) (value : Raw) : Raw :=
  match raw with
  | .object fields =>
      if fields.any (fun entry => entry.1 == name) then
        .object (fields.map fun entry =>
          if entry.1 == name then (name, value) else entry)
      else .object (fields ++ [(name, value)])
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

private def enumSetterParameter : Raw := rawObject [
  ("kind", rawText "ParmVarDecl"), ("id", rawText "0x15"),
  ("name", rawText "error"), ("type", rawObject [("qualType", rawText "XMLError")])]

private def enumSetterField : Raw := rawObject [
  ("kind", rawText "MemberExpr"), ("isArrow", .bool true),
  ("valueCategory", rawText "lvalue"), ("name", rawText "_errorID"),
  ("type", rawObject [("qualType", rawText "XMLError")]),
  ("referencedMemberDecl", rawText fieldHandle.value),
  ("inner", .array [rawObject [("kind", rawText "CXXThisExpr")]])]

private def enumSetterRight (parameter : String) : Raw := rawObject [
  ("kind", rawText "DeclRefExpr"),
  ("type", rawObject [("qualType", rawText "XMLError")]),
  ("referencedDecl", rawObject [("id", rawText parameter)])]

private def enumSetterBinary (right : Raw) : Raw := rawObject [
  ("kind", rawText "BinaryOperator"), ("opcode", rawText "="),
  ("type", rawObject [("qualType", rawText "XMLError")]),
  ("inner", .array [enumSetterField, right])]

private def enumSetterBody (right : Raw) : Raw := rawObject [
  ("kind", rawText "CompoundStmt"),
  ("inner", .array [enumSetterBinary right])]

private def enumSetterAst (right : Raw) : Raw := rawObject [
  ("kind", rawText "CXXMethodDecl"), ("id", rawText methodHandle.value),
  ("inner", .array [enumSetterParameter, enumSetterBody right])]

private def enumSetterProfileRaw : Raw :=
  rawWithFieldOrAppend
    (rawWithField profileRaw "method_parameter_types"
      (.array [rawObject [("kind", rawText "enumeration"),
        ("declaration", rawText "0x13")]]))
    "method_parent" (rawText ownerHandle.value)

private def enumSetterFieldRow : DeclarationEvidenceRow :=
  {declarationRow fieldHandle.value "FieldDecl" fieldHandle.value with
    semanticContext := some ownerHandle,
    raw := rawObject [("field_parent", rawText ownerHandle.value)]}

private def enumSetterProbeWith (right : Raw) : DeclarationProbe :=
  {ast := enumSetterAst right, metadata := .object [],
    declarations := [
      {declarationRow methodHandle.value "CXXMethodDecl" methodHandle.value with
        raw := enumSetterProfileRaw},
      enumSetterFieldRow]}

private def enumSetterRepresentation : Option IntegralMemberEnumRepresentation :=
  (IntegralMemberEnumRepresentation.withOracle {
    field := fieldHandle, enum := h "0x13", name := "XMLError",
    constantCount := 20, explicitValueCount := 1, underlyingType := none} .unsignedInt).toOption

private def enumSetterEvidence : Option IntegralMemberEnumSetter :=
  match enumSetterRepresentation with
  | some representation =>
      match IntegralMemberEnumSetter.admit (enumSetterProbeWith (enumSetterRight "0x15"))
          methodHandle representation with
      | .ok setter => some setter
      | .error _ => none
  | none => none

private def enumSetterAccepted : Bool :=
  match enumSetterEvidence with
  | some setter =>
      setter.field == fieldHandle && setter.parameter == h "0x15" &&
        setter.fieldName == "_errorID" && setter.fieldType == "XMLError" &&
        setter.parameterType == "XMLError"
  | none => false

private def enumSetterWrongParameter : Bool :=
  match enumSetterRepresentation with
  | some representation =>
      match IntegralMemberEnumSetter.admit (enumSetterProbeWith (enumSetterRight "0x99"))
          methodHandle representation with
      | .error .parameterMismatch => true
      | _ => false
  | none => false

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

private def enumProfileSample : IntegralMemberEnumProfile := {
  field := h "0x12", enum := h "0x13", name := "XMLError",
  constantCount := 20, explicitValueCount := 1, underlyingType := none}

private def enumFieldAccessSample : IntegralMemberThisFieldAccess := {
  method := h "0x14", definition := h "0x15", owner := h "0x16", field := h "0x12",
  name := "_errorID", receiverType := "XMLError *", fieldType := "XMLError"}

private def enumRepresentationSample : Option IntegralMemberEnumRepresentation :=
  (IntegralMemberEnumRepresentation.withOracle enumProfileSample .unsignedInt).toOption

private def enumValueAccepted : Bool :=
  match enumRepresentationSample with
  | some representation =>
      match IntegralMemberEnumValue.evaluate enumFieldAccessSample representation .lp64
          ⟨.unsigned 32, 7⟩ with
      | .ok value => value.representation == representation && value.value == ⟨.unsigned 32, 7⟩
      | .error _ => false
  | none => false

private def enumValueWrongFormat : Bool :=
  match enumRepresentationSample with
  | some representation =>
      match IntegralMemberEnumValue.evaluate enumFieldAccessSample representation .lp64
          ⟨.signed 32, 7⟩ with
      | .error .underlyingTypeMismatch => true
      | _ => false
  | none => false

private def enumValueWrongField : Bool :=
  match enumRepresentationSample with
  | some representation =>
      match IntegralMemberEnumValue.evaluate
          {enumFieldAccessSample with field := h "0x99"} representation .lp64
          ⟨.unsigned 32, 7⟩ with
      | .error .fieldMismatch => true
      | _ => false
  | none => false

private def enumValueBadProfile : Bool :=
  match enumRepresentationSample with
  | some representation =>
      match IntegralMemberEnumValue.evaluate enumFieldAccessSample representation
          {TargetProfile.lp64 with intWidth := 0} ⟨.unsigned 32, 7⟩ with
      | .error .invalidProfile => true
      | _ => false
  | none => false

private def enumValueInvalid : Bool :=
  match enumRepresentationSample with
  | some representation =>
      match IntegralMemberEnumValue.evaluate enumFieldAccessSample representation .lp64
          ⟨.unsigned 32, 4294967296⟩ with
      | .error (.invalidValue .outOfRange) => true
      | _ => false
  | none => false

private def enumReadAccess : IntegralMemberThisFieldAccess := {
  method := methodHandle, definition := methodHandle, owner := ownerHandle,
  field := fieldHandle, name := "value", receiverType := "Owner *", fieldType := "XMLError"}

private def enumReadProfile : IntegralMemberEnumProfile :=
  {enumProfileSample with field := fieldHandle}

private def enumReadRepresentation : Option IntegralMemberEnumRepresentation :=
  (IntegralMemberEnumRepresentation.withOracle enumReadProfile .unsignedInt).toOption

private def enumProjection : ClassReceiverProjection := {
  hierarchy := hierarchy, objects := [0], receiverPath := [],
  snapshot := {
    memory := {
      profile := .lp64,
      objects := {objects := [
        {duration := .automatic, type := .record ownerHandle, phase := .aliveInitialized},
        {duration := .automatic, type := .builtin .unsignedInt, phase := .aliveInitialized}]},
      values := [none, some ⟨.unsigned 32, 7⟩]},
    object := 0, member := 1, field := fieldHandle}}

private def enumSetterWriteAccepted : Bool :=
  match enumSetterEvidence with
  | some setter =>
      let access : IntegralMemberThisFieldAccess := {
        method := methodHandle, definition := methodHandle, owner := ownerHandle,
        field := fieldHandle, name := "_errorID", receiverType := "Owner *",
        fieldType := "XMLError", methodName := "set"}
      match IntegralMemberEnumSetter.write setter access enumProjection
          ⟨.unsigned 32, 9⟩ with
      | .ok memory => memory.values == [none, some ⟨.unsigned 32, 9⟩]
      | .error _ => false
  | none => false

private def enumSetterWriteWrongField : Bool :=
  match enumSetterEvidence with
  | some setter =>
      let access : IntegralMemberThisFieldAccess := {
        method := methodHandle, definition := methodHandle, owner := ownerHandle,
        field := h "0x99", name := "_errorID", receiverType := "Owner *",
        fieldType := "XMLError", methodName := "set"}
      match IntegralMemberEnumSetter.write setter access enumProjection
          ⟨.unsigned 32, 9⟩ with
      | .error .fieldMismatch => true
      | _ => false
  | none => false

private def enumReadAccepted : Bool :=
  match enumReadRepresentation with
  | some representation =>
      match IntegralMemberEnumValue.read enumReadAccess representation enumProjection with
      | .ok (memory, value) =>
          memory == enumProjection.snapshot.memory && value.value == ⟨.unsigned 32, 7⟩
      | .error _ => false
  | none => false

private def enumReadWrongObject : Bool :=
  match enumReadRepresentation with
  | some representation =>
      let bad := {enumProjection with
        snapshot := {enumProjection.snapshot with object := 1}}
      match IntegralMemberEnumValue.read enumReadAccess representation bad with
      | .error (.projection .wrongReceiver) => true
      | _ => false
  | none => false

private def enumReadWrongStorage : Bool :=
  match enumReadRepresentation with
  | some representation =>
      let bad := {enumProjection with snapshot := {enumProjection.snapshot with
        memory := {enumProjection.snapshot.memory with
          objects := {objects := (enumProjection.snapshot.memory.objects.objects.modify 1
            (fun object => {object with type := .builtin .int}))},
          values := [none, some ⟨.signed 32, 7⟩]}}}
      match IntegralMemberEnumValue.read enumReadAccess representation bad with
      | .error (.projection (.getter .malformedSnapshot)) => true
      | _ => false
  | none => false

private def enumWriteAccepted : Bool :=
  match enumReadRepresentation with
  | some representation =>
      match IntegralMemberEnumValue.write enumReadAccess representation enumProjection
          ⟨.unsigned 32, 9⟩ with
      | .ok memory =>
          memory.values == [none, some ⟨.unsigned 32, 9⟩]
      | .error _ => false
  | none => false

private def enumWriteWrongFormat : Bool :=
  match enumReadRepresentation with
  | some representation =>
      match IntegralMemberEnumValue.write enumReadAccess representation enumProjection
          ⟨.signed 32, 9⟩ with
      | .error (.value .underlyingTypeMismatch) => true
      | _ => false
  | none => false

private def enumWriteWrongProjection : Bool :=
  match enumReadRepresentation with
  | some representation =>
      let bad := {enumProjection with
        snapshot := {enumProjection.snapshot with object := 1}}
      match IntegralMemberEnumValue.write enumReadAccess representation bad
          ⟨.unsigned 32, 9⟩ with
      | .error (.projection .wrongReceiver) => true
      | _ => false
  | none => false

private def enumWriteReadOnly : Bool :=
  match enumReadRepresentation with
  | some representation =>
      let readOnly := {enumProjection with
        snapshot := {enumProjection.snapshot with readOnly := true}}
      match IntegralMemberEnumValue.write enumReadAccess representation readOnly
          ⟨.unsigned 32, 9⟩ with
      | .error (.getter .constReceiver) => true
      | _ => false
  | none => false

private def enumOracleError (underlying : CppIntType) :
    Option IntegralMemberEnumRepresentationError :=
  match IntegralMemberEnumRepresentation.withOracle enumProfileSample underlying with
  | .ok _ => none
  | .error error => some error

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

private def enumCallAccess : IntegralMemberThisFieldAccess :=
  {enumReadAccess with methodName := "read"}

private def enumCallRepresentation : IntegralMemberEnumRepresentation :=
  enumReadRepresentation.getD {profile := enumReadProfile, underlying := .unsignedInt}

private def enumSetterCallAccess : IntegralMemberThisFieldAccess := {
  method := methodHandle, definition := methodHandle, owner := ownerHandle,
  field := fieldHandle, name := "_errorID", receiverType := "Owner *",
  fieldType := "XMLError", methodName := "set"}

private def enumSetterCallSyntax : IntegralMemberCallSyntax := {
  method := methodHandle, receiver := receiverHandle, receiverType := "Owner *",
  resultType := "void", name := "set", canonicalMethod := methodHandle}

private def enumSetterCallArgument : IntegralMemberEnumValue :=
  {representation := enumSetterRepresentation.getD
      {profile := enumReadProfile, underlying := .unsignedInt},
    value := ⟨.unsigned 32, 9⟩}

private def rawEnumArgument (id type parameter : String) : Raw := rawObject [
  ("kind", rawText "DeclRefExpr"), ("id", rawText id),
  ("type", rawObject [("qualType", rawText type)]),
  ("referencedDecl", rawObject [("id", rawText parameter)])]

private def enumArgumentAccepted : Bool :=
  match enumSetterRepresentation with
  | some representation =>
      match IntegralMemberEnumArgument.admit
          (rawEnumArgument "0x20" "XMLError" "0x21") representation with
      | .ok argument =>
          argument.occurrence == h "0x20" && argument.type == .enumeration (h "0x13") &&
            argument.declaration == h "0x21"
      | .error _ => false
  | none => false

private def enumArgumentWrongType : Bool :=
  match enumSetterRepresentation with
  | some representation =>
      match IntegralMemberEnumArgument.admit
          (rawEnumArgument "0x20" "int" "0x21") representation with
      | .error .unsupportedType => true
      | _ => false
  | none => false

private def enumArgumentBindAccepted : Bool :=
  match enumSetterRepresentation with
  | some representation =>
      match IntegralMemberEnumArgument.admit
          (rawEnumArgument "0x20" "XMLError" "0x21") representation with
      | .ok argument =>
          match IntegralMemberEnumArgument.bindTo argument (h "0x15")
              (.enumeration (h "0x13")) with
          | .ok bound => bound.parameter == h "0x15"
          | .error _ => false
      | .error _ => false
  | none => false

private def enumSetterSourceArgument : Option IntegralMemberEnumArgument :=
  match enumSetterRepresentation with
  | some representation =>
      (IntegralMemberEnumArgument.admit
        (rawEnumArgument "0x20" "XMLError" "0x21") representation).toOption
  | none => none

private def enumArgumentValueAccepted : Bool :=
  match enumSetterRepresentation, enumSetterSourceArgument with
  | some representation, some argument =>
      match IntegralMemberEnumArgument.evaluate argument representation .lp64
          ⟨.unsigned 32, 9⟩ with
      | .ok value => value.representation == representation && value.value == ⟨.unsigned 32, 9⟩
      | .error _ => false
  | _, _ => false

private def enumArgumentValueWrongFormat : Bool :=
  match enumSetterRepresentation, enumSetterSourceArgument with
  | some representation, some argument =>
      match IntegralMemberEnumArgument.evaluate argument representation .lp64
          ⟨.signed 32, 9⟩ with
      | .error .underlyingTypeMismatch => true
      | _ => false
  | _, _ => false

private def enumArgumentValueWrongEnum : Bool :=
  match enumSetterRepresentation, enumSetterSourceArgument with
  | some representation, some argument =>
      let wrong := {argument with type := .enumeration (h "0x99")}
      match IntegralMemberEnumArgument.evaluate wrong representation .lp64
          ⟨.unsigned 32, 9⟩ with
      | .error .argumentMismatch => true
      | _ => false
  | _, _ => false

private def enumSetterCallObserved : Option Int :=
  match enumSetterEvidence with
  | some setter =>
      match enumSetterSourceArgument with
      | some sourceArgument =>
        match IntegralMemberEnumSetterCall.bindWithArgumentValue enumSetterCallSyntax setter
            enumSetterCallAccess receiverHandle sourceArgument ⟨.unsigned 32, 9⟩ enumProjection with
        | .ok call =>
            match call.invoke with
            | .ok memory => memory.values[1]?.bind id |>.map (fun value => value.value)
            | .error _ => none
        | .error _ => none
      | none => none
  | none => none

private def enumSetterCallArgumentError : Option IntegralMemberEnumSetterCallError :=
  match enumSetterEvidence with
  | some setter =>
      let wrong := {enumSetterCallArgument with
        representation := {enumSetterCallArgument.representation with underlying := .int}}
      match IntegralMemberEnumSetterCall.bind enumSetterCallSyntax setter
          enumSetterCallAccess receiverHandle wrong enumProjection with
      | .error reason => some reason
      | .ok _ => none
  | none => none

private def enumSetterCallValueError : Option IntegralMemberEnumSetterCallError :=
  match enumSetterEvidence, enumSetterSourceArgument with
  | some setter, some sourceArgument =>
      match IntegralMemberEnumSetterCall.bindWithArgumentValue enumSetterCallSyntax setter
          enumSetterCallAccess receiverHandle sourceArgument ⟨.signed 32, 9⟩ enumProjection with
      | .error reason => some reason
      | .ok _ => none
  | _, _ => none

private def enumSetterCallResultError : Option IntegralMemberEnumSetterCallError :=
  match enumSetterEvidence with
  | some setter =>
      let bad := {enumSetterCallSyntax with resultType := "int"}
      match IntegralMemberEnumSetterCall.bind bad setter enumSetterCallAccess receiverHandle
          enumSetterCallArgument enumProjection with
      | .error reason => some reason
      | .ok _ => none
  | none => none

private def enumCallObserved : Option Int :=
  match IntegralMemberCallSyntax.admit (rawCallWithResult methodHandle.value
      receiverHandle.value "read" "XMLError") with
  | .error _ => none
  | .ok callSyntax =>
      match IntegralMemberEnumCall.bind callSyntax enumCallAccess enumCallRepresentation
          receiverHandle enumProjection with
      | .error _ => none
      | .ok call =>
          match call.invoke with
          | .ok (_, value) => some value.value.value
          | .error _ => none

private def enumCallResultError : Option IntegralMemberEnumCallError :=
  match IntegralMemberCallSyntax.admit (rawCall methodHandle.value receiverHandle.value "read") with
  | .error _ => none
  | .ok callSyntax =>
      match IntegralMemberEnumCall.bind callSyntax enumCallAccess enumCallRepresentation
          receiverHandle enumProjection with
      | .error reason => some reason
      | .ok _ => none

private def enumCallReceiverError : Option IntegralMemberEnumCallError :=
  match IntegralMemberCallSyntax.admit (rawCallWithResult methodHandle.value
      receiverHandle.value "read" "XMLError") with
  | .error _ => none
  | .ok callSyntax =>
      match IntegralMemberEnumCall.bind callSyntax enumCallAccess enumCallRepresentation
          (h "0x99") enumProjection with
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
#guard enumSetterAccepted
#guard enumSetterWrongParameter
#guard enumSetterWriteAccepted
#guard enumSetterWriteWrongField
#guard enumArgumentAccepted
#guard enumArgumentWrongType
#guard enumArgumentBindAccepted
#guard enumArgumentValueAccepted
#guard enumArgumentValueWrongFormat
#guard enumArgumentValueWrongEnum
#guard methodBody.map (fun body =>
    (body.canonical, body.definition, body.bodyKind)) ==
    some (methodHandle, h "0x11", "CompoundStmt")
#guard (IntegralMemberEnumRepresentation.withOracle enumProfileSample .unsignedInt).toOption.map
    (fun representation => (representation.profile.name, representation.underlying)) ==
    some ("XMLError", .unsignedInt)
#guard enumOracleError .boolean == some .booleanUnderlying
#guard IntegralMemberEnumRepresentation.withOracle
    {enumProfileSample with underlyingType := some "int"} .unsignedInt matches
    .error .oracleDisagrees
#guard enumValueAccepted
#guard enumValueWrongFormat
#guard enumValueWrongField
#guard enumValueBadProfile
#guard enumValueInvalid
#guard enumReadAccepted
#guard enumReadWrongObject
#guard enumReadWrongStorage
#guard enumWriteAccepted
#guard enumWriteWrongFormat
#guard enumWriteWrongProjection
#guard enumWriteReadOnly
#guard enumSetterCallObserved == some 9
#guard enumSetterCallArgumentError == some .argumentRepresentationMismatch
#guard enumSetterCallValueError == some (.argumentValueMismatch .underlyingTypeMismatch)
#guard enumSetterCallResultError == some .resultTypeMismatch
#guard enumCallObserved == some 7
#guard enumCallResultError == some .resultTypeMismatch
#guard enumCallReceiverError == some .receiverMismatch
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
