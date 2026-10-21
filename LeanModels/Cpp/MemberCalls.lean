import LeanModels.Cpp.ClassSubobjects

namespace LeanModels.Cpp

/-- A source-backed direct zero-argument call on an existing receiver.
The receiver and method handles are provenance; execution uses the already
validated getter and caller-supplied object projection. -/
structure IntegralMemberCallSyntax where
  method : FrontendHandle
  receiver : FrontendHandle
  receiverType : String
  resultType : String
  name : String
  /-- Canonical method identity, initially the occurrence handle. -/
  canonicalMethod : FrontendHandle := method
  /-- Whether the source receiver uses `->` (`false` means direct `.` access). -/
  receiverIsArrow : Bool := true
  /-- Direct receiver conversions retained from the AST, outermost first. -/
  receiverCast : List String := []
  /-- A pointer-valued data member used as the receiver, when present. -/
  receiverField : Option FrontendHandle := none
  /-- The declaration supplying the base object of `receiverField`. -/
  receiverBase : Option FrontendHandle := none
  /-- Source spelling of `receiverField`, when present. -/
  receiverFieldName : Option String := none
  deriving Repr, BEq, Inhabited

/-- Typed evidence for the first member-call argument slice. This is a direct
`IntegerLiteral`, before any implicit conversion or overload selection. The
frontend spelling is retained alongside the normalized builtin type so a
caller cannot silently replace the source type with a guessed one. -/
structure IntegralMemberIntegerArgument where
  occurrence : FrontendHandle
  sourceType : String
  type : CppTypeEvidence
  value : Nat
  deriving Repr, BEq, Inhabited

/-- A method parameter witness selected from the canonical declaration row and
its retained AST children. The declaration handle and ordinal are both kept:
the type list alone is insufficient to bind an argument to a source parameter.
-/
structure IntegralMemberParameterEvidence where
  method : FrontendHandle
  parameter : FrontendHandle
  ordinal : Nat
  name : Option String
  sourceType : String
  type : CppTypeEvidence
  deriving Repr, BEq, Inhabited

/-- The canonical method-level profile needed before a member call can be
considered for execution. This is still frontend evidence: it does not lower
or run the method body. -/
structure IntegralMemberMethodProfile where
  method : FrontendHandle
  resultType : CppTypeEvidence
  parameters : List CppTypeEvidence
  isConst : Bool
  isStatic : Bool
  bodyKind : String
  deriving Repr, BEq, Inhabited

/-- The canonical-to-defining relation for a method whose canonical row is
declaration-only. The body handle is retained separately; it is never guessed
from a name or from the first redeclaration. -/
structure IntegralMemberMethodBody where
  canonical : FrontendHandle
  definition : FrontendHandle
  bodyKind : String
  deriving Repr, BEq, Inhabited

inductive IntegralMemberIntegerArgumentError where
  | notIntegerLiteral
  | missingOccurrence
  | malformedType
  | unsupportedType
  | malformedValue
  | missingParameter
  | parameterTypeMismatch
  | missingMethod
  | malformedMethodSignature
  | missingParameterEvidence
  | conflictingParameterEvidence
  deriving Repr, BEq, Inhabited

inductive IntegralMemberMethodProfileError where
  | missingMethod
  | conflictingMethod
  | malformedSignature
  | unsupportedFlags
  | missingBody
  | unsupportedBody
  deriving Repr, BEq, Inhabited

inductive IntegralMemberMethodBodyError where
  | missingCanonical
  | missingDefinition
  | ambiguousDefinition
  | conflictingDefinition
  | malformedDefinition
  | unsupportedDefinition
  deriving Repr, BEq, Inhabited

structure IntegralMemberBoundIntegerArgument where
  argument : IntegralMemberIntegerArgument
  parameter : FrontendHandle
  parameterType : CppTypeEvidence
  deriving Repr, BEq, Inhabited

namespace IntegralMemberIntegerArgument

private partial def rawNodesById (wanted : String) : Raw → List Raw
  | node@(.object fields) =>
      let here := if node.text "id" == some wanted then [node] else []
      here ++ fields.flatMap (fun (_, value) => rawNodesById wanted value)
  | .array values => values.flatMap (rawNodesById wanted)
  | _ => []

private def parameterRaws (raw : Raw) :
    Except IntegralMemberIntegerArgumentError (List Raw) :=
  match raw.field "inner" with
  | some (.array children) =>
      pure (children.filter (·.text "kind" == some "ParmVarDecl"))
  | _ => throw .malformedMethodSignature

/-- Recover one parameter from a canonical method's explicit metadata and AST
parameter child. Repeated or absent method/parameter evidence refuses instead
of guessing an ordinal or declaration identity. -/
def parameter (probe : DeclarationProbe) (method : FrontendHandle) (ordinal : Nat) :
    Except IntegralMemberIntegerArgumentError IntegralMemberParameterEvidence := do
  let rows := probe.declarations.filter (fun row =>
    row.id == method && row.kind == "CXXMethodDecl" && row.canonical == method)
  let row :: rest := rows | throw .missingMethod
  unless rest.all (· == row) do throw .conflictingParameterEvidence
  let parameterTypes ← match row.raw.field "method_parameter_types" with
    | some (.array values) => values.mapM (fun value =>
        match parseCppTypeEvidence value with
        | .ok type => pure type
        | .error _ => throw .malformedMethodSignature)
    | _ => throw .malformedMethodSignature
  let nodes := (rawNodesById method.value probe.ast).filter
    (·.text "kind" == some "CXXMethodDecl")
  let node :: restNodes := nodes | throw .missingMethod
  unless restNodes.all (· == node) do throw .conflictingParameterEvidence
  let parameters ← parameterRaws node
  unless parameters.length == parameterTypes.length do
    throw .malformedMethodSignature
  let some parameterType := parameterTypes[ordinal]? | throw .missingParameterEvidence
  let some parameterRaw := parameters[ordinal]? | throw .missingParameterEvidence
  let parameter ← match parameterRaw.field "id" with
    | some (.string value) =>
        match parseFrontendHandle value with
        | .ok handle => pure handle
        | .error _ => throw .missingParameterEvidence
    | _ => throw .missingParameterEvidence
  let sourceType ← match parameterRaw.field "type" with
    | some type => match type.text "qualType" with
        | some value => if value.isEmpty then throw .malformedMethodSignature else pure value
        | none => throw .malformedMethodSignature
    | none => throw .malformedMethodSignature
  unless sourceType == "int" && parameterType == .builtin .int do
    throw .parameterTypeMismatch
  pure ⟨method, parameter, ordinal, parameterRaw.text "name", sourceType, parameterType⟩

/-- Admit exactly the direct `int` literal slice priced by the member-call
census. Cast wrappers, boolean/character literals, and non-`int` spellings
remain outside this evidence tier. -/
def admit (raw : Raw) :
    Except IntegralMemberIntegerArgumentError IntegralMemberIntegerArgument := do
  unless raw.text "kind" == some "IntegerLiteral" do
    throw .notIntegerLiteral
  let occurrence ← match raw.field "id" with
    | some (.string value) =>
        match parseFrontendHandle value with
        | .ok handle => pure handle
        | .error _ => throw .missingOccurrence
    | _ => throw .missingOccurrence
  let sourceType ← match raw.field "type" with
    | some type => match type.text "qualType" with
        | some value => if value == "int" then pure value else throw .unsupportedType
        | none => throw .malformedType
    | none => throw .malformedType
  let value ← match raw.field "value" with
    | some (.string value) =>
        match value.toNat? with
        | some value => pure value
        | none => throw .malformedValue
    | _ => throw .malformedValue
  pure {occurrence, sourceType, type := .builtin .int, value}

/-- Bind a retained literal to an explicitly supplied parameter declaration.
No lookup, overload resolution, conversion, or execution occurs here. The
parameter identity and type must come from a separately validated method
signature; this function only checks the narrow exact-`int` boundary. -/
def bind (argument : IntegralMemberIntegerArgument) (parameter : FrontendHandle)
    (parameterType : CppTypeEvidence) :
    Except IntegralMemberIntegerArgumentError IntegralMemberBoundIntegerArgument := do
  unless !parameter.value.isEmpty do throw .missingParameter
  unless parameterType == .builtin .int do throw .parameterTypeMismatch
  pure {argument, parameter, parameterType}

/-- Bind against the parameter witness produced by `parameter`; this is the
only argument-to-parameter operation in the evidence tier. -/
def bindTo (argument : IntegralMemberIntegerArgument)
    (parameter : IntegralMemberParameterEvidence) :
    Except IntegralMemberIntegerArgumentError IntegralMemberBoundIntegerArgument := do
  unless argument.type == parameter.type && argument.sourceType == parameter.sourceType do
    throw .parameterTypeMismatch
  pure {argument, parameter := parameter.parameter, parameterType := parameter.type}

end IntegralMemberIntegerArgument

namespace IntegralMemberMethodProfile

private def parseTypeList (raw : Raw) :
    Except IntegralMemberMethodProfileError (List CppTypeEvidence) :=
  match raw.field "method_parameter_types" with
  | some (.array values) => values.mapM (fun value =>
      match parseCppTypeEvidence value with
      | .ok type => pure type
      | .error _ => throw .malformedSignature)
  | _ => throw .malformedSignature

private def boolField (raw : Raw) (name : String) :
    Except IntegralMemberMethodProfileError Bool :=
  (evidenceBool raw name).mapError (fun _ => .malformedSignature)

private def natField (raw : Raw) (name : String) :
    Except IntegralMemberMethodProfileError Nat :=
  (evidenceNat raw name).mapError (fun _ => .malformedSignature)

/-- Preserve one canonical instance-method signature and body ownership. Every
frontend flag that would change dispatch, parameter count, or body ownership
is checked explicitly; missing fields refuse rather than defaulting. -/
def admit (probe : DeclarationProbe) (method : FrontendHandle) :
    Except IntegralMemberMethodProfileError IntegralMemberMethodProfile := do
  let rows := probe.declarations.filter (fun row =>
    row.id == method && row.kind == "CXXMethodDecl" && row.canonical == method)
  let row :: rest := rows | throw .missingMethod
  unless rest.all (· == row) do throw .conflictingMethod
  let raw := row.raw
  let _ ← (requireEvidenceText raw "method_shape_api"
      "CXXMethodDecl receiver shape v1").mapError (fun _ => .malformedSignature)
  let _ ← (requireEvidenceText raw "method_signature_api"
      "FunctionDecl return and parameter projection v1").mapError (fun _ => .malformedSignature)
  let definition ← boolField raw "definition"
  let bodyPresent ← boolField raw "body_present"
  let defaulted ← boolField raw "defaulted"
  let deleted ← boolField raw "deleted_as_written"
  let skipped ← boolField raw "function_has_skipped_body"
  let pending ← boolField raw "function_will_have_body"
  let defining ← boolField raw "function_has_defining_attr"
  let lateParsed ← boolField raw "function_late_template_parsed"
  let explicitlyDefaulted ← boolField raw "function_explicitly_defaulted"
  let attributeCount ← natField raw "function_attribute_count"
  unless definition && bodyPresent && !defaulted && !deleted && !skipped && !pending &&
      !defining && !lateParsed && !explicitlyDefaulted && attributeCount == 0 do
    throw .unsupportedBody
  let some bodyKind ← (evidenceNullableText raw "own_body_kind").mapError
      (fun _ => .malformedSignature)
    | throw .missingBody
  let some bodyOwner ← (evidenceNullableHandle raw "own_body_owner").mapError
      (fun _ => .malformedSignature)
    | throw .missingBody
  unless bodyKind == "CompoundStmt" && bodyOwner == method do throw .unsupportedBody
  let isConst ← boolField raw "method_const"
  let isStatic ← boolField raw "method_static"
  let volatile ← boolField raw "method_volatile"
  let virtual ← boolField raw "method_virtual"
  let pureMethod ← boolField raw "method_pure"
  let variadic ← boolField raw "method_variadic"
  let exceptionSpec ← natField raw "method_exception_spec"
  let refQualifier ← natField raw "method_ref_qualifier"
  unless !isStatic && !volatile && !virtual && !pureMethod && !variadic &&
      exceptionSpec == 0 && refQualifier == 0 do throw .unsupportedFlags
  let parameters ← parseTypeList raw
  let resultType ← match raw.field "method_result_type" with
    | some value => match parseCppTypeEvidence value with
        | .ok type => pure type
        | .error _ => throw .malformedSignature
    | none => throw .malformedSignature
  pure {method, resultType, parameters, isConst, isStatic, bodyKind}

end IntegralMemberMethodProfile

namespace IntegralMemberMethodBody

private def boolField (raw : Raw) (name : String) :
    Except IntegralMemberMethodBodyError Bool :=
  (evidenceBool raw name).mapError (fun _ => .malformedDefinition)

private def bodyCandidate (canonical : FrontendHandle) (row : DeclarationEvidenceRow) :
    Except IntegralMemberMethodBodyError IntegralMemberMethodBody := do
  let raw := row.raw
  let definition ← boolField raw "definition"
  let bodyPresent ← boolField raw "body_present"
  unless definition && bodyPresent do throw .malformedDefinition
  let skipped ← boolField raw "function_has_skipped_body"
  let pending ← boolField raw "function_will_have_body"
  let defining ← boolField raw "function_has_defining_attr"
  let lateParsed ← boolField raw "function_late_template_parsed"
  let explicitlyDefaulted ← boolField raw "function_explicitly_defaulted"
  let defaulted ← boolField raw "defaulted"
  let deleted ← boolField raw "deleted_as_written"
  let attributeCount ← (evidenceNat raw "function_attribute_count").mapError
    (fun _ => .malformedDefinition)
  unless !skipped && !pending && !defining && !lateParsed && !explicitlyDefaulted &&
      !defaulted && !deleted && attributeCount == 0 do throw .unsupportedDefinition
  let some bodyKind ← (evidenceNullableText raw "own_body_kind").mapError
      (fun _ => .malformedDefinition)
    | throw .malformedDefinition
  let some owner ← (evidenceNullableHandle raw "own_body_owner").mapError
      (fun _ => .malformedDefinition)
    | throw .malformedDefinition
  unless bodyKind == "CompoundStmt" && owner == row.id do throw .malformedDefinition
  pure {canonical, definition := row.id, bodyKind}

/-- Resolve a canonical method to exactly one clean defining occurrence. The
canonical row itself may be declaration-only; duplicate identical evidence is
harmless, while distinct defining handles or conflicting rows refuse. -/
def admit (probe : DeclarationProbe) (canonical : FrontendHandle) :
    Except IntegralMemberMethodBodyError IntegralMemberMethodBody := do
  let canonicalRows := probe.declarations.filter (fun row =>
    row.id == canonical && row.kind == "CXXMethodDecl" && row.canonical == canonical)
  if canonicalRows.isEmpty then throw .missingCanonical
  let candidates := probe.declarations.filter (fun row =>
    row.kind == "CXXMethodDecl" && row.canonical == canonical &&
      row.raw.field "definition" == some (.bool true))
  let candidateIds := candidates.map (·.id) |>.eraseDups
  let some definition := candidateIds.head? | throw .missingDefinition
  unless candidateIds.tail.isEmpty do throw .ambiguousDefinition
  let matching := candidates.filter (·.id == definition)
  match matching with
  | [] => throw .missingDefinition
  | row :: rest =>
      unless rest.all (·.raw == row.raw) do throw .conflictingDefinition
      bodyCandidate canonical row

end IntegralMemberMethodBody

/-- A typed receiver/member witness for the first direct `this->field` access
in a defining body. It is a precondition for an object-backed frame, not a
layout or offset calculation. -/
structure IntegralMemberThisFieldAccess where
  method : FrontendHandle
  definition : FrontendHandle
  owner : FrontendHandle
  field : FrontendHandle
  name : String
  receiverType : String
  fieldType : String
  deriving Repr, BEq, Inhabited

inductive IntegralMemberThisFieldAccessError where
  | missingMethod
  | missingOwner
  | missingFirstField
  | malformedReceiver
  | malformedField
  | fieldMismatch
  deriving Repr, BEq, Inhabited

namespace IntegralMemberThisFieldAccess

private partial def rawNodesById (wanted : String) : Raw → List Raw
  | node@(.object fields) =>
      (if node.text "id" == some wanted then [node] else []) ++
        fields.flatMap (fun (_, value) => rawNodesById wanted value)
  | .array values => values.flatMap (rawNodesById wanted)
  | _ => []

private def directThis (raw : Raw) : Bool :=
  match raw.field "inner" with
  | some (.array [base]) => base.text "kind" == some "CXXThisExpr"
  | _ => false

private partial def firstThisMember : Raw → Option Raw
  | node@(.object fields) =>
      if node.text "kind" == some "MemberExpr" && directThis node then some node
      else fields.firstM (fun (_, value) => firstThisMember value)
  | .array values => values.firstM firstThisMember
  | _ => none

private def handleField (raw : Raw) (name : String) :
    Except IntegralMemberThisFieldAccessError FrontendHandle :=
  match raw.field name with
  | some (.string value) =>
      (parseFrontendHandle value).mapError (fun _ => .fieldMismatch)
  | some value => (evidenceHandle value "id").mapError (fun _ => .fieldMismatch)
  | none => throw .fieldMismatch

/-- Require the first direct `this->field` in a selected body to agree with the
method's parent and the field's declaration evidence. No field offset or value
is fabricated. -/
def admit (probe : DeclarationProbe) (body : IntegralMemberMethodBody) :
    Except IntegralMemberThisFieldAccessError IntegralMemberThisFieldAccess := do
  let some methodRow := probe.declarations.find? (fun row =>
    row.id == body.definition && row.kind == "CXXMethodDecl")
    | throw .missingMethod
  let owner ← handleField methodRow.raw "method_parent" |>.mapError (fun _ => .missingOwner)
  let methodNodes := (rawNodesById body.definition.value probe.ast).filter
    (·.text "kind" == some "CXXMethodDecl")
  let some method := methodNodes.head? | throw .missingMethod
  let some member := firstThisMember method | throw .missingFirstField
  unless member.field "isArrow" == some (.bool true) &&
      member.text "valueCategory" == some "lvalue" do throw .malformedReceiver
  let receiverType ← match member.field "type" with
    | some type => match type.text "qualType" with
        | some value => if value.isEmpty then throw .malformedReceiver else pure value
        | none => throw .malformedReceiver
    | none => throw .malformedReceiver
  let field ← handleField member "referencedMemberDecl"
  let name ← match member.text "name" with
    | some value => if value.isEmpty then throw .malformedField else pure value
    | none => throw .malformedField
  let fieldType ← match member.field "type" with
    | some type => match type.text "qualType" with
        | some value => if value.isEmpty then throw .malformedField else pure value
        | none => throw .malformedField
    | none => throw .malformedField
  let fieldRows := probe.declarations.filter (fun row =>
    row.id == field && row.kind == "FieldDecl")
  let fieldRow :: rest := fieldRows | throw .fieldMismatch
  unless rest.all (fun row => row.raw == fieldRow.raw && row.semanticContext == fieldRow.semanticContext) do
    throw .fieldMismatch
  unless fieldRow.semanticContext == some owner do throw .fieldMismatch
  let fieldParent ← handleField fieldRow.raw "field_parent"
  unless fieldParent == owner do throw .fieldMismatch
  pure ⟨body.canonical, body.definition, owner, field, name, receiverType, fieldType⟩

end IntegralMemberThisFieldAccess

/-- Enum metadata needed to read `_errorID`. The frontend's declaration handle
and enumerator count are retained, while an absent fixed underlying type stays
absent instead of being guessed as `int`. -/
structure IntegralMemberEnumProfile where
  field : FrontendHandle
  enum : FrontendHandle
  name : String
  constantCount : Nat
  explicitValueCount : Nat
  underlyingType : Option String
  deriving Repr, BEq, Inhabited

inductive IntegralMemberEnumProfileError where
  | malformedTypeEvidence
  | missingFieldType
  | nonEnumerationField
  | missingEnum
  | malformedEnum
  | conflictingEnum
  deriving Repr, BEq, Inhabited

namespace IntegralMemberEnumProfile

private partial def rawNodesById (wanted : String) : Raw → List Raw
  | node@(.object fields) =>
      (if node.text "id" == some wanted then [node] else []) ++
        fields.flatMap (fun (_, value) => rawNodesById wanted value)
  | .array values => values.flatMap (rawNodesById wanted)
  | _ => []

private def enumConstants (raw : Raw) :
    Except IntegralMemberEnumProfileError (List Raw) :=
  match raw.field "inner" with
  | some (.array children) => pure (children.filter (·.text "kind" == some "EnumConstantDecl"))
  | _ => throw .malformedEnum

private partial def containsKind (wanted : String) : Raw → Bool
  | node@(.object fields) =>
      node.text "kind" == some wanted || fields.any (fun (_, value) => containsKind wanted value)
  | .array values => values.any (containsKind wanted)
  | _ => false

private def explicitValue (raw : Raw) : Bool :=
  containsKind "ConstantExpr" raw || (raw.field "value").isSome

/-- Recover the enum identity and explicit-value census for a typed field. No
underlying representation is supplied when Clang did not retain one. -/
def admit (probe : DeclarationProbe) (access : IntegralMemberThisFieldAccess) :
    Except IntegralMemberEnumProfileError IntegralMemberEnumProfile := do
  let typeRows ← match parseValidatedTypeEvidence probe with
    | .ok rows => pure rows
    | .error _ => throw .malformedTypeEvidence
  let some (.enumeration enum) := typeEvidenceFor typeRows access.field
    | throw .missingFieldType
  let nodes := (rawNodesById enum.value probe.ast).filter
    (·.text "kind" == some "EnumDecl")
  let node :: rest := nodes | throw .missingEnum
  unless rest.all (· == node) do throw .conflictingEnum
  let name ← match node.text "name" with
    | some value => if value.isEmpty then throw .malformedEnum else pure value
    | none => throw .malformedEnum
  let constants ← enumConstants node
  let underlyingType ← match node.field "fixedUnderlyingType" with
    | none => pure none
    | some value => match value.text "qualType" with
        | some spelling => pure (some spelling)
        | none => throw .malformedEnum
  pure ⟨access.field, enum, name, constants.length, constants.countP explicitValue,
    underlyingType⟩

end IntegralMemberEnumProfile

/-- A caller-supplied representation choice for an enum whose frontend
metadata omitted its fixed underlying type. This is an oracle input, not a
fact recovered from the AST. -/
structure IntegralMemberEnumRepresentation where
  profile : IntegralMemberEnumProfile
  underlying : CppIntType
  deriving Repr, BEq, Inhabited

inductive IntegralMemberEnumRepresentationError where
  | booleanUnderlying
  | oracleDisagrees
  deriving Repr, BEq, Inhabited

namespace IntegralMemberEnumRepresentation

def underlyingName : CppIntType → String
  | .char => "char"
  | .signedChar => "signed char"
  | .unsignedChar => "unsigned char"
  | .short => "short"
  | .unsignedShort => "unsigned short"
  | .int => "int"
  | .unsignedInt => "unsigned int"
  | .long => "long"
  | .unsignedLong => "unsigned long"
  | .longLong => "long long"
  | .unsignedLongLong => "unsigned long long"
  | .boolean => "bool"

/-- Apply an explicit integral underlying-type oracle. If the profile contains
a retained fixed spelling, the oracle must agree; an absent spelling remains
an oracle choice. -/
def withOracle (profile : IntegralMemberEnumProfile) (underlying : CppIntType) :
    Except IntegralMemberEnumRepresentationError IntegralMemberEnumRepresentation := do
  unless underlying != .boolean do throw .booleanUnderlying
  match profile.underlyingType with
  | some retained =>
      unless retained == underlyingName underlying do throw .oracleDisagrees
  | none => pure ()
  pure {profile, underlying}

end IntegralMemberEnumRepresentation

inductive IntegralMemberCallSyntaxError where
  | notMemberCall
  | malformedChildren
  | unsupportedReceiver
  | unsupportedArguments
  | missingMethodHandle
  | unsupportedMethod
  | canonicalMethodMissing
  | canonicalMethodAmbiguous
  | canonicalMethodTargetMissing
  | canonicalMethodTargetMismatch
  | missingReceiverHandle
  | missingThisOwner
  | malformedReceiverType
  | malformedResultType
  | malformedName
  deriving Repr, BEq, Inhabited

namespace IntegralMemberCallSyntax

private def children (raw : Raw) : Option (List Raw) := do
  let .array values ← raw.field "inner" | none
  pure values

private def oneChild (raw : Raw) : Except IntegralMemberCallSyntaxError Raw :=
  match children raw with
  | some [child] => .ok child
  | _ => .error .malformedChildren

private def basePath (raw : Raw) : Except IntegralMemberCallSyntaxError (List String) :=
  match raw.field "path" with
  | some (.array edges) => do
      unless !edges.isEmpty do throw .unsupportedReceiver
      edges.mapM fun edge => do
        let some name := edge.text "name" | throw .unsupportedReceiver
        unless cppIdentifier name do throw .unsupportedReceiver
        pure name
  | _ => throw .unsupportedReceiver

private def callChild (raw : Raw) : Except IntegralMemberCallSyntaxError Raw :=
  match children raw with
  | some [child] => .ok child
  | some (_ :: _ :: _) => .error .unsupportedArguments
  | _ => .error .malformedChildren

private def resultSpelling (raw : Raw) : Except IntegralMemberCallSyntaxError String :=
  match raw.field "type" with
  | some type => match type.text "qualType" with
      | some value => if value.isEmpty then .error .malformedResultType else .ok value
      | none => .error .malformedResultType
  | none => .error .malformedResultType

private partial def containsThis (raw : Raw) : Bool :=
  raw.text "kind" == some "CXXThisExpr" ||
    (((raw.field "inner").bind Raw.array?).getD []).any containsThis

private partial def receiverDeclRef (raw : Raw) :
    Except IntegralMemberCallSyntaxError (Raw × List String) :=
  match raw.text "kind" with
  | some "DeclRefExpr" => pure (raw, [])
  | some "ImplicitCastExpr" => do
      let some cast := raw.text "castKind" | throw .unsupportedReceiver
      let child ← oneChild raw
      let (decl, casts) ← receiverDeclRef child
      if cast == "UncheckedDerivedToBase" then
        let path ← basePath raw
        pure (decl, (cast ++ "[" ++ String.intercalate "::" path ++ "]") :: casts)
      else
        unless cast == "LValueToRValue" || cast == "NoOp" do throw .unsupportedReceiver
        pure (decl, cast :: casts)
  | _ => throw .unsupportedReceiver

private def pointerSpelling (value : String) : Bool :=
  match value.toList.reverse with
  | '*' :: _ => true
  | _ => false

private structure ReceiverPlan where
  receiver : FrontendHandle
  casts : List String
  field : Option FrontendHandle := none
  base : Option FrontendHandle := none
  fieldName : Option String := none

private def receiverPlan (raw : Raw) : Except IntegralMemberCallSyntaxError ReceiverPlan := do
  match raw.text "kind" with
  | some "ImplicitCastExpr" =>
      let some cast := raw.text "castKind" | throw .unsupportedReceiver
      let child ← oneChild raw
      if cast == "LValueToRValue" && child.text "kind" == some "MemberExpr" then
        unless child.text "valueCategory" == some "lvalue" do throw .unsupportedReceiver
        unless child.field "isArrow" == some (.bool true) do throw .unsupportedReceiver
        let outerType ← match raw.field "type" with
          | some type => match type.text "qualType" with
              | some value => pure value
              | none => throw .unsupportedReceiver
          | none => throw .unsupportedReceiver
        let fieldName ← match child.text "name" with
          | some value => pure value
          | none => throw .unsupportedReceiver
        unless cppIdentifier fieldName do throw .unsupportedReceiver
        let fieldHandle ← match child.field "referencedMemberDecl" with
          | some (.string id) =>
              (parseFrontendHandle id).mapError (fun _ => .unsupportedReceiver)
          | some value => do
              unless value.text "kind" == some "FieldDecl" do throw .unsupportedReceiver
              (evidenceHandle value "id").mapError (fun _ => .unsupportedReceiver)
          | none => throw .unsupportedReceiver
        let fieldType ← match child.field "type" with
          | some type => match type.text "qualType" with
              | some value => if pointerSpelling value then pure value else throw .unsupportedReceiver
              | none => throw .unsupportedReceiver
          | none => throw .unsupportedReceiver
        unless outerType == fieldType do throw .unsupportedReceiver
        let baseRaw ← oneChild child
        let (base, baseCasts) ← receiverDeclRef baseRaw
        let some baseReferenced := base.field "referencedDecl"
          | throw .missingReceiverHandle
        let baseHandle ← (evidenceHandle baseReferenced "id").mapError
          (fun _ => .missingReceiverHandle)
        let receiver := fieldHandle
        let field := some fieldHandle
        let base := some baseHandle
        let fieldName := some fieldName
        pure {receiver, casts := (cast :: baseCasts), field, base, fieldName}
      else
        let (decl, casts) ← receiverDeclRef raw
        let some referenced := decl.field "referencedDecl"
          | throw .missingReceiverHandle
        let receiver ← (evidenceHandle referenced "id").mapError
          (fun _ => .missingReceiverHandle)
        pure {receiver, casts, field := none, base := none, fieldName := none}
  | some "DeclRefExpr" =>
      let (decl, casts) ← receiverDeclRef raw
      let some referenced := decl.field "referencedDecl"
        | throw .missingReceiverHandle
      let receiver ← (evidenceHandle referenced "id").mapError
        (fun _ => .missingReceiverHandle)
      pure {receiver, casts, field := none, base := none, fieldName := none}
  | _ => throw .unsupportedReceiver

def admit (raw : Raw) :
    Except IntegralMemberCallSyntaxError IntegralMemberCallSyntax := do
  unless raw.text "kind" == some "CXXMemberCallExpr" do
    throw .notMemberCall
  let member ← callChild raw
  unless member.text "kind" == some "MemberExpr" do
    throw .malformedChildren
  let receiverIsArrow ← match member.field "isArrow" with
    | some (.bool value) => pure value
    | _ => throw .unsupportedReceiver
  unless member.text "valueCategory" == some "prvalue" do
    throw .unsupportedReceiver
  let name ← match member.text "name" with
    | some value => pure value
    | none => throw .malformedName
  unless cppIdentifier name do throw .malformedName
  let method ← match member.field "referencedMemberDecl" with
    | some (.string id) =>
        (parseFrontendHandle id).mapError (fun _ => .missingMethodHandle)
    | some value => do
        unless value.text "kind" == some "CXXMethodDecl" do throw .unsupportedMethod
        (evidenceHandle value "id").mapError (fun _ => .missingMethodHandle)
    | none => throw .missingMethodHandle
  let receiverRawOuter ← oneChild member
  if containsThis receiverRawOuter then throw .missingThisOwner
  let receiverPlan ← receiverPlan receiverRawOuter
  let receiverType ← match receiverRawOuter.field "type" with
    | some type => match type.text "qualType" with
        | some value => if value.isEmpty then throw .malformedReceiverType else pure value
        | none => throw .malformedReceiverType
    | none => throw .malformedReceiverType
  let resultType ← resultSpelling raw
  pure {(default : IntegralMemberCallSyntax) with
    method := method, receiver := receiverPlan.receiver, receiverType := receiverType,
    resultType := resultType, name := name, canonicalMethod := method,
    receiverIsArrow := receiverIsArrow, receiverCast := receiverPlan.casts,
    receiverField := receiverPlan.field, receiverBase := receiverPlan.base,
    receiverFieldName := receiverPlan.fieldName}

/-- Resolve one retained method occurrence to exactly one canonical probe handle. -/
def resolveCanonical (probe : DeclarationProbe) (evidence : IntegralMemberCallSyntax) :
    Except IntegralMemberCallSyntaxError IntegralMemberCallSyntax := do
  let candidates : List FrontendHandle := probe.declarations.filterMap fun row =>
    if row.id == evidence.method && row.kind == "CXXMethodDecl" then some row.canonical else none
  match candidates.eraseDups with
  | [] => throw .canonicalMethodMissing
  | [canonical] =>
      unless probe.declarations.any (fun row =>
          row.id == canonical && row.kind == "CXXMethodDecl" && row.canonical == canonical) do
        throw .canonicalMethodTargetMissing
      unless probe.declarations.any (fun row =>
          row.id == canonical && row.kind == "CXXMethodDecl" && row.canonical == canonical &&
            row.raw.text "name" == some evidence.name) do
        throw .canonicalMethodTargetMismatch
      pure {evidence with canonicalMethod := canonical}
  | _ => throw .canonicalMethodAmbiguous

/-- Admit a raw call and resolve its declaration occurrence through probe evidence. -/
def admitResolved (probe : DeclarationProbe) (raw : Raw) :
    Except IntegralMemberCallSyntaxError IntegralMemberCallSyntax := do
  resolveCanonical probe (← admit raw)

end IntegralMemberCallSyntax

structure IntegralMemberCall where
  getter : IntegralMemberGetter
  projection : ClassReceiverProjection
  syntaxEvidence : IntegralMemberCallSyntax
  deriving Repr, BEq, Inhabited

inductive IntegralMemberCallError where
  | methodMismatch
  | nameMismatch
  | receiverMismatch
  | canonicalMethodMismatch
  | receiverTypeMismatch
  | resultTypeMismatch
  | projection (reason : ClassProjectionError)
  deriving Repr, BEq, Inhabited

namespace IntegralMemberCall

private def projectionReceiverType (projection : ClassReceiverProjection) (isArrow : Bool) :
    Except IntegralMemberCallError String := do
  let slots ← projection.hierarchy.slots.mapError
    (fun reason => IntegralMemberCallError.projection (.hierarchy reason))
  let some slot := slots.find? (·.path == projection.receiverPath)
    | throw (.projection .absentReceiver)
  let some shape := projection.hierarchy.classes.find? (·.declaration == slot.declaration)
    | throw (.projection .malformedWorld)
  unless !shape.name.isEmpty do throw .receiverTypeMismatch
  pure (shape.name ++ if isArrow then " *" else "")

private def resultMatches : CppIntType → String → Bool
  | .boolean, "bool" => true
  | .char, "char" => true
  | .signedChar, "signed char" => true
  | .unsignedChar, "unsigned char" => true
  | .short, "short" | .short, "short int" => true
  | .unsignedShort, "unsigned short" | .unsignedShort, "unsigned short int" => true
  | .int, "int" => true
  | .unsignedInt, "unsigned" | .unsignedInt, "unsigned int" => true
  | .long, "long" | .long, "long int" => true
  | .unsignedLong, "unsigned long" | .unsignedLong, "unsigned long int" => true
  | .longLong, "long long" | .longLong, "long long int" => true
  | .unsignedLongLong, "unsigned long long" |
      .unsignedLongLong, "unsigned long long int" => true
  | _, _ => false

/-- Bind source handles to an already admitted getter and receiver projection.
No overload lookup or method selection is performed here. -/
def bind (evidence : IntegralMemberCallSyntax) (getter : IntegralMemberGetter)
    (receiver : FrontendHandle)
    (projection : ClassReceiverProjection) :
    Except IntegralMemberCallError IntegralMemberCall := do
  unless evidence.method == ⟨getter.occurrence.id⟩ do throw .methodMismatch
  unless evidence.canonicalMethod == getter.canonical do throw .canonicalMethodMismatch
  unless getter.occurrence.name == some evidence.name do throw .nameMismatch
  unless evidence.receiver == receiver do throw .receiverMismatch
  projection.check getter |>.mapError .projection
  let receiverType ← projectionReceiverType projection evidence.receiverIsArrow
  unless evidence.receiverType == receiverType do throw .receiverTypeMismatch
  unless resultMatches getter.result evidence.resultType do throw .resultTypeMismatch
  pure {getter, projection, syntaxEvidence := evidence}

def invoke (call : IntegralMemberCall) :
    Except IntegralMemberCallError (IntegralObjectStore × IntegralValue) :=
  call.projection.invoke call.getter |>.mapError .projection

end IntegralMemberCall

end LeanModels.Cpp
