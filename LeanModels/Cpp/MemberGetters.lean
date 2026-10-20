import LeanModels.Cpp.RecordObjects
import LeanModels.Cpp.ExpressionEvidence

namespace LeanModels.Cpp

/-- A source-validated single member read, with inner-to-outer value conversions. -/
structure IntegralMemberGetter where
  occurrence : Declaration
  owner : FrontendHandle
  field : IntegralRecordField
  isConst : Bool
  conversions : List CppIntType
  result : CppIntType
  deriving Repr, BEq, Inhabited

def integralMemberViewType (type : CppTypeEvidence) (constant : Bool) : CppTypeEvidence :=
  if constant then
    match type with
    | .qualified _ false base => .qualified true false base
    | _ => .qualified true false type
  else type

namespace MemberGetterAdmission

private def children (raw : Raw) : Except String (List Raw) :=
  match raw.field "inner" with
  | none => pure []
  | some (.array values) => pure values
  | _ => throw "member getter: malformed children"

private def onlyChild (raw : Raw) : Except String Raw := do
  let [child] ← children raw | throw "member getter: requires exactly one child"
  pure child

private def methodShape (raw : Raw) (owner : FrontendHandle) :
    Except String (Bool × CppIntType) := do
  requireEvidenceText raw "method_shape_api" "CXXMethodDecl receiver shape v1"
  requireEvidenceText raw "method_signature_api" "FunctionDecl return and parameter projection v1"
  unless (← evidenceHandle raw "method_parent") == owner &&
      !(← evidenceBool raw "method_static") && !(← evidenceBool raw "method_volatile") &&
      !(← evidenceBool raw "method_virtual") && !(← evidenceBool raw "method_pure") &&
      (← evidenceNat raw "method_ref_qualifier") == 0 do
    throw "member getter: unsupported receiver or dispatch qualification"
  unless !(← evidenceBool raw "method_variadic") &&
      (← evidenceNat raw "method_exception_spec") == 0 &&
      (← evidenceField raw "method_parameter_types") == .array [] do
    throw "member getter: parameters or exception specification"
  let .builtin result ← parseCppTypeEvidence (← evidenceField raw "method_result_type")
    | throw "member getter: requires a builtin integral result"
  pure (← evidenceBool raw "method_const", result)

private def receiverSource (artifact : Artifact) (probe : DeclarationProbe)
    (owner : FrontendHandle) : Except String (Raw × FrontendHandle) := do
  let row ← localFunctionRow probe owner.value
  localFunctionScope probe owner true
  requireEvidenceText row.raw "record_shape_api" "CXXRecordDecl aggregate member shape v1"
  unless (← evidenceBool row.raw "record_complete") &&
      !(← evidenceBool row.raw "record_union") &&
      (← evidenceNat row.raw "record_base_count") == 0 do
    throw "member getter: incomplete, union or base-class receiver"
  let candidates := (artifact.declarationsById owner.value).filterMap fun declaration => do
    let raw ← artifact.ast.atPath declaration.path
    if raw.field "completeDefinition" == some (.bool true) then some (declaration, raw) else none
  let (occurrence, raw) :: rest := candidates
    | throw "member getter: complete receiver source is absent"
  unless rest.all (fun (_, other) => other == raw) do
    throw "member getter: conflicting receiver source"
  unless raw.text "kind" == some "CXXRecordDecl" &&
      raw.text "name" == row.raw.text "name" &&
      (raw.text "tagUsed" == some "class" || raw.text "tagUsed" == some "struct") do
    throw "member getter: inconsistent receiver source"
  match raw.field "bases" with
  | none | some (.array []) => pure ()
  | _ => throw "member getter: source receiver has bases"
  let lexical ← lexicalContextChainEvidence artifact probe occurrence
  let semantic ← semanticContextChainEvidence artifact probe occurrence
  unless lexical.map (·.value) == occurrence.lexicalParents.reverse do
    throw "member getter: inconsistent receiver ancestry"
  lexical.forM (fun handle => localFunctionScopeSource artifact probe handle true)
  semantic.forM (fun handle => localFunctionScopeSource artifact probe handle true)
  let attributes := (← children raw).filter (fun child =>
    (child.text "kind").any (·.endsWith "Attr"))
  unless attributes.length == (← evidenceNat row.raw "record_attribute_count") &&
      attributes.all (·.text "kind" == some "VisibilityAttr") do
    throw "member getter: unsupported receiver attribute"
  let fields := (← children raw).filter (·.text "kind" == some "FieldDecl")
  unless fields.length == (← evidenceNat row.raw "record_field_count") do
    throw "member getter: incomplete receiver field census"
  pure (raw, ← canonicalRootEvidence probe occurrence)

private def selectedField (probe : DeclarationProbe) (types : List TypeEvidenceRow)
    (owner : FrontendHandle) (recordRaw : Raw) (target : FrontendHandle) :
    Except String IntegralRecordField := do
  let fields := (← children recordRaw).filter (·.text "kind" == some "FieldDecl")
  let some (raw, index) := fields.zipIdx.find? (fun (field, _) => field.text "id" == some target.value)
    | throw "member getter: selected field is not a direct member"
  let row ← localFunctionRow probe target.value
  unless row.kind == "FieldDecl" && row.canonical == target &&
      row.semanticContext == some owner && row.lexicalContext == some owner do
    throw "member getter: selected field identity or owner"
  requireEvidenceText row.raw "field_shape_api" "FieldDecl member shape v1"
  unless (← evidenceHandle row.raw "field_parent") == owner &&
      (← evidenceNat row.raw "field_index") == index &&
      !(← evidenceBool row.raw "field_bitfield") &&
      (← evidenceNat row.raw "field_attribute_count") == 0 do
    throw "member getter: bit-field, attributed or inconsistent field"
  let isMutable ← evidenceBool row.raw "field_mutable"
  unless isMutable == (← optionalSourceBool raw "mutable") &&
      !(← optionalSourceBool raw "isBitfield") &&
      (← evidenceBool row.raw "field_initializer") ==
        (← optionalSourceBool raw "hasInClassInitializer") do
    throw "member getter: inconsistent source field flags"
  unless (← children raw).all (fun child =>
      !(child.text "kind").any (·.endsWith "Attr")) do
    throw "member getter: source field has attributes"
  let name ← evidenceText raw "name"
  unless cppIdentifier name && row.raw.text "name" == some name do
    throw "member getter: unsupported field name"
  let typed :: rest := types.filter (·.occurrence == target)
    | throw "member getter: missing structured field type"
  unless typed.canonical == target && rest.all (·.type == typed.type) do
    throw "member getter: conflicting field type"
  let some (_, constant) := recordIntegralKind typed.type
    | throw "member getter: nonintegral or volatile field"
  if isMutable && constant then throw "member getter: mutable const field"
  pure {declaration := target, name, type := typed.type, isMutable}

private structure ReadExpression where
  field : IntegralRecordField
  type : CppTypeEvidence
  loaded : Bool
  conversions : List CppIntType

private partial def readExpression (probe : DeclarationProbe) (types : List TypeEvidenceRow)
    (expressions : List CppExpressionTypeEvidence) (owner root : FrontendHandle)
    (recordRaw : Raw) (constant : Bool) (raw : Raw) : Except String ReadExpression := do
  let type ← expressionTypeFor expressions raw
  match raw.text "kind" with
  | some "ParenExpr" =>
      let value ← readExpression probe types expressions owner root recordRaw constant (← onlyChild raw)
      unless value.type == type do throw "member getter: parenthesis type mismatch"
      pure value
  | some "ImplicitCastExpr" =>
      let value ← readExpression probe types expressions owner root recordRaw constant (← onlyChild raw)
      let .builtin destination := type | throw "member getter: nonintegral conversion result"
      match raw.text "castKind" with
      | some "LValueToRValue" =>
          unless !value.loaded && (recordIntegralKind value.type).map Prod.fst == some destination do
            throw "member getter: invalid lvalue conversion"
          pure {value with type, loaded := true}
      | some "IntegralCast" | some "IntegralToBoolean" =>
          unless value.loaded && (match value.type with | .builtin _ => true | _ => false) do
            throw "member getter: conversion requires an integral value"
          if raw.text "castKind" == some "IntegralToBoolean" && destination != .boolean then
            throw "member getter: boolean conversion result"
          pure {value with type, conversions := value.conversions ++ [destination]}
      | _ => throw "member getter: unsupported conversion"
  | some "MemberExpr" =>
      unless (← evidenceBool raw "isArrow") && raw.text "valueCategory" == some "lvalue" do
        throw "member getter: requires an arrow member lvalue"
      let base ← onlyChild raw
      unless base.text "kind" == some "CXXThisExpr" && (← children base).isEmpty &&
          base.text "valueCategory" == some "prvalue" do
        throw "member getter: requires direct this"
      let thisType : CppTypeEvidence := .pointer (integralMemberViewType (.record root) constant)
      unless (← expressionTypeFor expressions base) == thisType do
        throw "member getter: this type disagrees with receiver"
      let field ← selectedField probe types owner recordRaw (← evidenceHandle raw "referencedMemberDecl")
      unless raw.text "name" == some field.name do
        throw "member getter: selected member name disagrees with declaration"
      unless type == integralMemberViewType field.type (constant && !field.isMutable) do
        throw "member getter: member access qualification mismatch"
      pure {field, type, loaded := false, conversions := []}
  | _ => throw "member getter: unsupported return expression"

def withEvidence (probe : DeclarationProbe) (types : List TypeEvidenceRow)
    (expressions : List CppExpressionTypeEvidence) (path : List Nat) :
    Except String IntegralMemberGetter := do
  let admitted ← admitLocalInstanceMethodDeclaration probe path
  unless admitted.parameters.isEmpty do throw "member getter: parameters are outside the profile"
  let .compound body := admitted.form | throw "member getter: requires an owned compound body"
  let artifact : Artifact := {
    sourceFile := "", sourceSha256 := "", frontend := .null,
    dependencies := [], ast := probe.ast}
  let row ← localFunctionRow probe admitted.occurrence.id
  let some owner := row.semanticContext | throw "member getter: missing record context"
  let (constant, result) ← methodShape row.raw owner
  for handle in (← canonicalPredecessorChainEvidence probe admitted.occurrence) do
    unless (← methodShape (← localFunctionRow probe handle.value).raw owner) == (constant, result) do
      throw "member getter: inconsistent method redeclaration"
  let (recordRaw, root) ← receiverSource artifact probe owner
  let returned ← onlyChild body
  unless returned.text "kind" == some "ReturnStmt" do throw "member getter: requires one return"
  let expression ← readExpression probe types (expressionTypeRowsFor body expressions)
    owner root recordRaw constant (← onlyChild returned)
  unless expression.loaded && expression.type == .builtin result do
    throw "member getter: return conversion or value category mismatch"
  pure {
    occurrence := admitted.occurrence, owner := root, field := expression.field,
    isConst := constant, conversions := expression.conversions, result}

end MemberGetterAdmission

def admitIntegralMemberGetter (probe : DeclarationProbe) (path : List Nat) :
    Except String IntegralMemberGetter := do
  let types ← parseValidatedTypeEvidence probe
  let some expressions ← parseValidatedExpressionTypeEvidence probe
    | throw "member getter: requires expression type evidence"
  MemberGetterAdmission.withEvidence probe types expressions path

/-- A caller-supplied projection of an already existing complete object/member pair.
The ownership relation is an explicit state input; no layout or constructor is inferred. -/
structure IntegralMemberSnapshot where
  memory : IntegralObjectStore
  object : ObjectId
  member : ObjectId
  field : FrontendHandle
  readOnly : Bool := false
  deriving Repr, BEq, Inhabited

inductive MemberGetterError where
  | malformedGetter
  | malformedSnapshot
  | wrongReceiver
  | constReceiver
  | object (reason : ObjectError)
  | integral (reason : IntegralObjectError)
  | conversion (reason : String)
  deriving Repr, BEq, Inhabited

def IntegralMemberGetter.valid (getter : IntegralMemberGetter) : Bool :=
  getter.field.declaration != getter.owner && cppIdentifier getter.field.name &&
    (recordIntegralKind getter.field.type).any (fun (kind, constant) =>
      (!getter.field.isMutable || !constant) &&
      getter.conversions.getLast?.getD kind == getter.result)

def IntegralMemberSnapshot.bind (snapshot : IntegralMemberSnapshot)
    (getter : IntegralMemberGetter) : Except MemberGetterError IntegralObjectRef := do
  unless snapshot.memory.profile.valid &&
      snapshot.memory.values.length == snapshot.memory.objects.objects.length &&
      snapshot.object != snapshot.member && snapshot.field == getter.field.declaration do
    throw .malformedSnapshot
  let rootType ← (snapshot.memory.objects.readType snapshot.object).mapError MemberGetterError.object
  let actualConst ← match rootType with
    | .record owner =>
        unless owner == getter.owner do throw .wrongReceiver
        pure false
    | .qualified true false (.record owner) =>
        unless owner == getter.owner do throw .wrongReceiver
        pure true
    | _ => throw .wrongReceiver
  if (actualConst || snapshot.readOnly) && !getter.isConst then throw .constReceiver
  let some root := snapshot.memory.objects.object? snapshot.object | throw .malformedSnapshot
  let some member := snapshot.memory.objects.object? snapshot.member | throw .malformedSnapshot
  unless root.duration == member.duration &&
      member.type == integralMemberViewType getter.field.type (actualConst && !getter.field.isMutable) &&
      snapshot.memory.values[snapshot.object]? == some none do throw .malformedSnapshot
  let _ ← (snapshot.memory.objects.readType snapshot.member).mapError MemberGetterError.object
  let accessType := integralMemberViewType getter.field.type
    ((actualConst || snapshot.readOnly || getter.isConst) && !getter.field.isMutable)
  pure {object := snapshot.member, type := accessType}

def memberGetterConvert (profile : TargetProfile) : List CppIntType → IntegralValue →
    Except MemberGetterError IntegralValue
  | [], value => .ok value
  | kind :: rest, value => do
      let format ← match profile.format kind with
        | .ok format => pure format
        | _ => throw (.conversion "unavailable target format")
      let converted ← match integralConvert format value with
        | .ok converted => pure converted
        | _ => throw (.conversion "integral conversion refused")
      memberGetterConvert profile rest converted

def IntegralMemberGetter.evaluate (getter : IntegralMemberGetter) (snapshot : IntegralMemberSnapshot) :
    Except MemberGetterError IntegralValue := do
  unless getter.valid do throw .malformedGetter
  let access ← snapshot.bind getter
  let value ← (snapshot.memory.read access).mapError MemberGetterError.integral
  memberGetterConvert snapshot.memory.profile getter.conversions value

def IntegralMemberGetter.invoke (getter : IntegralMemberGetter) (snapshot : IntegralMemberSnapshot) :
    Except MemberGetterError (IntegralObjectStore × IntegralValue) :=
  (getter.evaluate snapshot).map fun value => (snapshot.memory, value)

theorem IntegralMemberGetter.invoke_memory (getter : IntegralMemberGetter)
    (snapshot : IntegralMemberSnapshot) (memory : IntegralObjectStore) (value : IntegralValue)
    (h : getter.invoke snapshot = .ok (memory, value)) : memory = snapshot.memory := by
  unfold invoke at h
  cases he : getter.evaluate snapshot with
  | error reason => simp [he, Except.map] at h
  | ok result => simp [he, Except.map] at h; exact h.1.symm

/-- Total successful invocation from valid caller-state observations, including failures
in the premises rather than interpreting failure as an arbitrary successful value. -/
theorem IntegralMemberGetter.invoke_of_read (getter : IntegralMemberGetter)
    (snapshot : IntegralMemberSnapshot) (access : IntegralObjectRef) (value result : IntegralValue)
    (valid : getter.valid = true) (bound : snapshot.bind getter = .ok access)
    (read : snapshot.memory.read access = .ok value)
    (converted : memberGetterConvert snapshot.memory.profile getter.conversions value = .ok result) :
    getter.invoke snapshot = .ok (snapshot.memory, result) := by
  simp [invoke, evaluate, valid, bound, read, converted, Except.map, Except.mapError,
    Except.bind, bind]

end LeanModels.Cpp
