import LeanModels.Cpp.MemberCalls

open Lean LeanModels.Cpp

/- A source-backed syntax census only. It validates the complete probe, walks
   retained AST children, and never executes a call or constructs a receiver. -/

private def jsonObject := Json.mkObj

private partial def memberCalls (raw : Raw) : List Raw :=
  let nested := (((raw.field "inner").bind Raw.array?).getD []).flatMap memberCalls
  if raw.text "kind" == some "CXXMemberCallExpr" then raw :: nested else nested

private def errorName : IntegralMemberCallSyntaxError → String
  | .notMemberCall => "not-member-call"
  | .malformedChildren => "malformed-children"
  | .unsupportedReceiver => "unsupported-receiver"
  | .unsupportedArguments => "unsupported-arguments"
  | .missingMethodHandle => "missing-method-handle"
  | .unsupportedMethod => "unsupported-method"
  | .canonicalMethodMissing => "canonical-method-missing"
  | .canonicalMethodAmbiguous => "canonical-method-ambiguous"
  | .canonicalMethodTargetMissing => "canonical-method-target-missing"
  | .canonicalMethodTargetMismatch => "canonical-method-target-mismatch"
  | .missingReceiverHandle => "missing-receiver-handle"
  | .missingThisOwner => "missing-this-owner"
  | .malformedReceiverType => "malformed-receiver-type"
  | .malformedResultType => "malformed-result-type"
  | .malformedName => "malformed-name"

private def counts (values : List String) : Json :=
  jsonObject (values.eraseDups.map fun value => (value, toJson (values.count value)))

private def integerArgumentErrorName :
    IntegralMemberIntegerArgumentError → String
  | .notIntegerLiteral => "not-integer-literal"
  | .missingOccurrence => "missing-occurrence"
  | .malformedType => "malformed-type"
  | .unsupportedType => "unsupported-type"
  | .malformedValue => "malformed-value"
  | .missingParameter => "missing-parameter"
  | .parameterTypeMismatch => "parameter-type-mismatch"
  | .missingMethod => "missing-method"
  | .malformedMethodSignature => "malformed-method-signature"
  | .missingParameterEvidence => "missing-parameter-evidence"
  | .conflictingParameterEvidence => "conflicting-parameter-evidence"

private def methodProfileErrorName :
    IntegralMemberMethodProfileError → String
  | .missingMethod => "missing-method"
  | .conflictingMethod => "conflicting-method"
  | .malformedSignature => "malformed-signature"
  | .unsupportedFlags => "unsupported-flags"
  | .missingBody => "missing-body"
  | .unsupportedBody => "unsupported-body"

private def methodBodyErrorName :
    IntegralMemberMethodBodyError → String
  | .missingCanonical => "missing-canonical"
  | .missingDefinition => "missing-definition"
  | .ambiguousDefinition => "ambiguous-definition"
  | .conflictingDefinition => "conflicting-definition"
  | .malformedDefinition => "malformed-definition"
  | .unsupportedDefinition => "unsupported-definition"

private def thisFieldErrorName :
    IntegralMemberThisFieldAccessError → String
  | .missingMethod => "missing-method"
  | .missingOwner => "missing-owner"
  | .missingFirstField => "missing-first-field"
  | .malformedReceiver => "malformed-receiver"
  | .malformedField => "malformed-field"
  | .fieldMismatch => "field-mismatch"

private def enumProfileErrorName :
    IntegralMemberEnumProfileError → String
  | .malformedTypeEvidence => "malformed-type-evidence"
  | .missingFieldType => "missing-field-type"
  | .nonEnumerationField => "non-enumeration-field"
  | .missingEnum => "missing-enum"
  | .malformedEnum => "malformed-enum"
  | .conflictingEnum => "conflicting-enum"

private def enumRepresentationErrorName :
    IntegralMemberEnumRepresentationError → String
  | .booleanUnderlying => "boolean-underlying"
  | .oracleDisagrees => "oracle-disagrees"

private def enumArgumentErrorName : IntegralMemberEnumArgumentError → String
  | .notDeclRef => "not-decl-ref"
  | .missingOccurrence => "missing-occurrence"
  | .malformedType => "malformed-type"
  | .unsupportedType => "unsupported-type"
  | .missingReferencedDeclaration => "missing-referenced-declaration"
  | .parameterTypeMismatch => "parameter-type-mismatch"
  | .missingMethod => "missing-method"
  | .malformedMethodSignature => "malformed-method-signature"
  | .missingParameterEvidence => "missing-parameter-evidence"
  | .conflictingParameterEvidence => "conflicting-parameter-evidence"

private def enumSetterErrorName :
    IntegralMemberEnumSetterError → String
  | .profile error => "profile:" ++ methodProfileErrorName error
  | .body error => "body:" ++ methodBodyErrorName error
  | .resultType => "result-type"
  | .parameterCount => "parameter-count"
  | .assignmentMissing => "assignment-missing"
  | .malformedAssignment => "malformed-assignment"
  | .missingOwner => "missing-owner"
  | .missingField => "missing-field"
  | .fieldMismatch => "field-mismatch"
  | .missingParameter => "missing-parameter"
  | .parameterMismatch => "parameter-mismatch"
  | .fieldTypeMismatch => "field-type-mismatch"
  | .parameterTypeMismatch => "parameter-type-mismatch"

private def memberMethodHandle (raw : Raw) : Option FrontendHandle := do
  let .array (member :: _) ← raw.field "inner" | none
  let referenced ← member.field "referencedMemberDecl"
  match referenced with
  | .string value => (parseFrontendHandle value).toOption
  | .object _ => (evidenceHandle referenced "id").toOption
  | _ => none

private def canonicalMethodHandle (probe : DeclarationProbe)
    (method : FrontendHandle) : Option FrontendHandle :=
  match (probe.declarations.filterMap fun row =>
      if row.id == method && row.kind == "CXXMethodDecl" then some row.canonical else none).eraseDups with
  | [canonical] => some canonical
  | _ => none

private partial def hasKind (wanted : String) (raw : Raw) : Bool :=
  raw.text "kind" == some wanted ||
    (((raw.field "inner").bind Raw.array?).getD []).any (hasKind wanted)

private partial def rawNodesById (wanted : String) : Raw → List Raw
  | node@(.object fields) =>
      (if node.text "id" == some wanted then [node] else []) ++
        fields.flatMap (fun (_, value) => rawNodesById wanted value)
  | .array values => values.flatMap (rawNodesById wanted)
  | _ => []

private def methodEnumResult (probe : DeclarationProbe) (method : FrontendHandle) :
    Except String FrontendHandle := do
  let rows := probe.declarations.filter (fun row =>
    row.id == method && row.kind == "CXXMethodDecl")
  let row :: rest := rows | throw "missing-method"
  unless rest.all (· == row) do throw "conflicting-method"
  let some raw := row.raw.field "method_result_type" | throw "missing-result-type"
  let type ← parseCppTypeEvidence raw |>.mapError (fun _ => "malformed-result-type")
  match type with
  | .enumeration enum => pure enum
  | _ => throw "non-enum-result"

private def methodEnumParameter (probe : DeclarationProbe) (method : FrontendHandle)
    (ordinal : Nat) : Except String FrontendHandle := do
  let rows := probe.declarations.filter (fun row =>
    row.id == method && row.kind == "CXXMethodDecl")
  let row :: rest := rows | throw "missing-method"
  unless rest.all (· == row) do throw "conflicting-method"
  let some (.array values) := row.raw.field "method_parameter_types"
    | throw "missing-parameter-types"
  let some value := values[ordinal]? | throw "missing-parameter"
  match parseCppTypeEvidence value with
  | .ok (.enumeration enum) => pure enum
  | .ok _ => throw "non-enum-parameter"
  | .error _ => throw "malformed-parameter-type"

private def enumResultName (probe : DeclarationProbe) (enum : FrontendHandle) :
    Except String String := do
  let nodes := (rawNodesById enum.value probe.ast).filter
    (·.text "kind" == some "EnumDecl")
  let node :: rest := nodes | throw "missing-enum"
  unless rest.all (· == node) do throw "conflicting-enum"
  let some name := node.text "name" | throw "malformed-enum"
  unless !name.isEmpty do throw "malformed-enum"
  pure name

private def rawResultSpelling (raw : Raw) : Option String := do
  let type ← raw.field "type"
  type.text "qualType"

private def enumGetterProfile (probe : DeclarationProbe) (method : FrontendHandle) :
    Except String String := do
  let canonical := canonicalMethodHandle probe method |>.getD method
  let body ← IntegralMemberMethodBody.admit probe canonical |>.mapError (fun _ => "body")
  let access ← IntegralMemberThisFieldAccess.admit probe body |>.mapError (fun _ => "field")
  let profile ← IntegralMemberEnumProfile.admit probe access |>.mapError (fun _ => "enum")
  let representation ← IntegralMemberEnumRepresentation.withOracle profile .unsignedInt |>.mapError
    (fun _ => "representation")
  let _ ← IntegralMemberEnumGetter.admit probe canonical representation |>.mapError
    (fun _ => "getter")
  pure profile.name


private partial def firstObjectEvent : Raw → Option String
  | node@(.object fields) =>
      match node.text "kind" with
      | some "MemberExpr" =>
          if hasKind "CXXThisExpr" node then
            some (s!"this-member:{node.text "name" |>.getD "<missing>"}")
          else firstObjectFields fields
      | some "CXXMemberCallExpr" => some "member-call"
      | some "CXXNewExpr" => some "allocation"
      | some "CXXDeleteExpr" => some "deallocation"
      | some "CXXConstructExpr" => some "construction"
      | _ => firstObjectFields fields
  | .array values => values.firstM firstObjectEvent
  | _ => none
where
  firstObjectFields : List (String × Raw) → Option String
    | [] => none
    | (name, value) :: rest =>
        if name == "inner" then
          match firstObjectEvent value with
          | some event => some event
          | none => firstObjectFields rest
        else firstObjectFields rest

private def methodBodyObjectEvent (probe : DeclarationProbe)
    (body : IntegralMemberMethodBody) : Option String := do
  let method ← (rawNodesById body.definition.value probe.ast).find?
    (·.text "kind" == some "CXXMethodDecl")
  let inner ← method.field "inner" |>.bind Raw.array?
  let compound ← inner.find? (·.text "kind" == some "CompoundStmt")
  firstObjectEvent compound

private partial def directThisFieldWrites : Raw → List String
  | node@(.object fields) =>
      let nested := fields.flatMap (fun (_, value) => directThisFieldWrites value)
      match node.text "kind", node.text "opcode", node.field "inner" with
      | some "BinaryOperator", some "=", some (.array (left :: _)) =>
          if left.text "kind" == some "MemberExpr" && hasKind "CXXThisExpr" left then
            (left.text "name" |>.getD "<missing>") :: nested
          else nested
      | _, _, _ => nested
  | .array values => values.flatMap directThisFieldWrites
  | _ => []

private def methodBodyThisFieldWrites (probe : DeclarationProbe)
    (body : IntegralMemberMethodBody) : List String :=
  match (rawNodesById body.definition.value probe.ast).find?
      (·.text "kind" == some "CXXMethodDecl") with
  | none => []
  | some method =>
      match method.field "inner" with
      | some (.array inner) =>
          match inner.find? (·.text "kind" == some "CompoundStmt") with
          | some compound => directThisFieldWrites compound
          | none => []
      | _ => []

private def directThisMember (raw : Raw) : Bool :=
  raw.text "kind" == some "MemberExpr" &&
    raw.field "isArrow" == some (.bool true) &&
    raw.text "valueCategory" == some "lvalue" &&
    match raw.field "inner" with
    | some (.array [base]) => base.text "kind" == some "CXXThisExpr"
    | _ => false

private partial def firstDirectThisFieldWrite : Raw → Option Raw
  | node@(.object fields) =>
      match node.text "kind", node.text "opcode", node.field "inner" with
      | some "BinaryOperator", some "=", some (.array (left :: _)) =>
          if directThisMember left then some left
          else fields.firstM (fun (_, value) => firstDirectThisFieldWrite value)
      | _, _, _ => fields.firstM (fun (_, value) => firstDirectThisFieldWrite value)
  | .array values => values.firstM firstDirectThisFieldWrite
  | _ => none

private def rawHandle? (raw : Raw) (name : String) : Option FrontendHandle := do
  match raw.field name with
  | some (.string value) => (parseFrontendHandle value).toOption
  | some value => (evidenceHandle value "id").toOption
  | none => none

private def rawQualType? (raw : Raw) : Option String := do
  let type ← raw.field "type"
  type.text "qualType"

private def enumSpellingMatches (spelling name : String) : Bool :=
  spelling == name || spelling == "enum " ++ name || spelling.endsWith ("::" ++ name)

private def enumArgumentShape (argument : Raw) (enumName : String) : Except String String :=
  match argument.text "kind" with
  | some "DeclRefExpr" => do
      let spelling ← match rawQualType? argument with
        | some spelling => pure spelling
        | none => throw "declref-missing-type"
      unless enumSpellingMatches spelling enumName do
        throw ("declref-type-mismatch:" ++ spelling)
      unless (rawHandle? argument "referencedDecl").isSome do
        throw "declref-missing-declaration"
      pure (s!"{enumName}:{spelling}:DeclRefExpr")
  | some kind =>
      if kind.endsWith "CastExpr" then
        throw (s!"{enumName}:cast:{kind}")
      else
        throw (s!"{enumName}:non-reference:{kind}")
  | none => throw (s!"{enumName}:non-reference:<missing>")

private def methodBodyThisFieldWriteAccess (probe : DeclarationProbe)
    (body : IntegralMemberMethodBody) : Option IntegralMemberThisFieldAccess := do
  let method ← (rawNodesById body.definition.value probe.ast).find?
    (·.text "kind" == some "CXXMethodDecl")
  let inner ← method.field "inner" |>.bind Raw.array?
  let compound ← inner.find? (·.text "kind" == some "CompoundStmt")
  let left ← firstDirectThisFieldWrite compound
  let owner ← probe.declarations.find? (fun row =>
    row.id == body.definition && row.kind == "CXXMethodDecl") |>.bind
    (fun row => rawHandle? row.raw "method_parent")
  let field ← rawHandle? left "referencedMemberDecl"
  let name ← left.text "name"
  let fieldType ← rawQualType? left
  let receiverType ← match left.field "inner" with
    | some (.array [base]) => rawQualType? base
    | _ => none
  pure ⟨body.canonical, body.definition, owner, field, name, receiverType, fieldType,
    method.text "name" |>.getD ""⟩

private partial def rawTree (raw : Raw) : String :=
  let kind := raw.text "kind" |>.getD "<missing>"
  let cast := raw.text "castKind" |>.map (fun value => ":" ++ value) |>.getD ""
  let children := match raw.field "inner" with
    | some (.array values) => values
    | _ => []
  if children.isEmpty then kind ++ cast
  else kind ++ cast ++ "(" ++ String.intercalate "," (children.map rawTree) ++ ")"

private def argumentShape (raw : Raw) : String :=
  match raw.field "inner" with
  | some (.array (_ :: arguments)) =>
      String.intercalate "," (arguments.map (fun argument => argument.text "kind" |>.getD "<missing>"))
  | _ => "<malformed>"

private def receiverFamily (raw : Raw) : String :=
  match raw.field "inner" with
  | some (.array (member :: _)) =>
      match member.field "inner" with
      | some (.array (base :: _)) =>
          if hasKind "CXXThisExpr" base then "this"
          else if hasKind "CXXMemberCallExpr" base then "member-call"
          else if hasKind "MemberExpr" base then "member"
          else if hasKind "ImplicitCastExpr" base then "cast"
          else base.text "kind" |>.getD "other"
      | _ => "missing-base"
  | _ => "malformed"

private def receiverShape (raw : Raw) : String :=
  match raw.field "inner" with
  | some (.array (member :: _)) =>
      let kind := member.text "kind" |>.getD "<missing>"
      let arrow := match member.field "isArrow" with
        | some (.bool true) => "arrow"
        | some (.bool false) => "dot"
        | _ => "arrow-missing"
      let category := member.text "valueCategory" |>.getD "<missing>"
      let bases := match member.field "inner" with
        | some (.array children) => String.intercalate "," (children.map rawTree)
        | _ => "<missing>"
      s!"{kind}|{arrow}|{category}|{bases}"
  | _ => "<malformed>"

private def emit (value : Json) : IO Unit := IO.println value.compress

private def refuse (stage reason : String) : IO UInt32 := do
  emit (jsonObject [
    ("format", toJson "cpp-member-call-census-1"),
    ("status", toJson "REFUSE"),
    ("stage", toJson stage),
    ("reason", toJson reason),
    ("execution", toJson "not-attempted")])
  return 2

private def census (probe : DeclarationProbe) : IO UInt32 := do
  let calls := memberCalls probe.ast
  let mut admitted := 0
  let mut refusals : List String := []
  let mut argumentShapes : List String := []
  let mut argumentTrees : List String := []
  let mut integerArgumentBindings : List String := []
  let mut integerArgumentRefusals : List String := []
  let mut integerMethodProfiles : List String := []
  let mut integerMethodProfileRefusals : List String := []
  let mut integerMethodBodies : List String := []
  let mut integerMethodBodyRefusals : List String := []
  let mut integerMethodObjectEvents : List String := []
  let mut integerMethodObjectRefusals : List String := []
  let mut integerMethodThisFields : List String := []
  let mut integerMethodThisFieldRefusals : List String := []
  let mut integerMethodThisFieldWrites : List String := []
  let mut integerMethodEnumProfiles : List String := []
  let mut integerMethodEnumProfileRefusals : List String := []
  let mut integerMethodEnumRepresentations : List String := []
  let mut integerMethodEnumRepresentationRefusals : List String := []
  let mut integerMethodEnumSetterProfiles : List String := []
  let mut integerMethodEnumSetterRefusals : List String := []
  let mut enumResultCalls : List String := []
  let mut enumResultRefusals : List String := []
  let mut enumArgumentShapes : List String := []
  let mut enumArgumentRefusals : List String := []
  let mut enumArgumentParameters : List String := []
  let mut enumArgumentParameterRefusals : List String := []
  let mut enumArgumentMethodProfiles : List String := []
  let mut enumArgumentMethodProfileRefusals : List String := []
  let mut enumArgumentMethodBodies : List String := []
  let mut enumArgumentMethodBodyRefusals : List String := []
  let mut enumArgumentMethodObjectEvents : List String := []
  let mut enumArgumentMethodObjectRefusals : List String := []
  let mut enumGetterProfiles : List String := []
  let mut enumGetterRefusals : List String := []
  let mut receiverShapes : List String := []
  let mut receiverFamilies : List String := []
  let mut reports : List Json := []
  for (raw, ordinal) in calls.zipIdx do
    match memberMethodHandle raw with
    | some method =>
        let canonical := canonicalMethodHandle probe method |>.getD method
        match raw.field "inner" with
        | some (.array (_ :: arguments)) =>
            for (argument, argumentOrdinal) in arguments.zipIdx do
              match methodEnumParameter probe canonical argumentOrdinal with
              | .ok enum =>
                  match enumResultName probe enum with
                  | .ok name =>
                      match IntegralMemberEnumArgument.parameter probe canonical argumentOrdinal
                          enum name with
                      | .ok parameter => enumArgumentParameters :=
                          (s!"{parameter.method.value}:{parameter.parameter.value}:" ++
                            s!"{parameter.ordinal}:{parameter.sourceType}") :: enumArgumentParameters
                      | .error error => enumArgumentParameterRefusals :=
                          enumArgumentErrorName error :: enumArgumentParameterRefusals
                      match IntegralMemberMethodProfile.admit probe canonical with
                      | .ok profile => enumArgumentMethodProfiles :=
                          profile.method.value :: enumArgumentMethodProfiles
                      | .error error => enumArgumentMethodProfileRefusals :=
                          methodProfileErrorName error :: enumArgumentMethodProfileRefusals
                      match IntegralMemberMethodBody.admit probe canonical with
                      | .ok body =>
                          enumArgumentMethodBodies :=
                            (s!"{body.canonical.value}:{body.definition.value}") ::
                              enumArgumentMethodBodies
                          match methodBodyObjectEvent probe body with
                          | some event => enumArgumentMethodObjectEvents :=
                              (s!"{body.canonical.value}:{event}") ::
                                enumArgumentMethodObjectEvents
                          | none => enumArgumentMethodObjectRefusals :=
                              "missing-first-object-event" :: enumArgumentMethodObjectRefusals
                      | .error error => enumArgumentMethodBodyRefusals :=
                          methodBodyErrorName error :: enumArgumentMethodBodyRefusals
                      match enumArgumentShape argument name with
                      | .ok shape => enumArgumentShapes := shape :: enumArgumentShapes
                      | .error reason => enumArgumentRefusals := reason :: enumArgumentRefusals
                  | .error reason => enumArgumentRefusals :=
                      ("enum:" ++ reason) :: enumArgumentRefusals
              | .error _ => pure ()
        | _ => pure ()
        match methodEnumResult probe (canonicalMethodHandle probe method |>.getD method) with
        | .ok enum =>
            let spelling := rawResultSpelling raw |>.getD "<missing>"
            match enumResultName probe enum, rawResultSpelling raw with
            | .ok name, some spelling =>
                if spelling == name || spelling == "enum " ++ name ||
                    spelling.endsWith ("::" ++ name) then
                  enumResultCalls := (s!"{name}:{spelling}") :: enumResultCalls
                else enumResultRefusals := "result-spelling-mismatch" :: enumResultRefusals
            | .error error, _ => enumResultRefusals := error :: enumResultRefusals
            | _, none => enumResultRefusals := "missing-result-spelling" :: enumResultRefusals
            match enumGetterProfile probe (canonicalMethodHandle probe method |>.getD method) with
            | .ok name => enumGetterProfiles := (s!"{name}:{spelling}") :: enumGetterProfiles
            | .error error => enumGetterRefusals := error :: enumGetterRefusals
        | .error error =>
            if error != "non-enum-result" && error != "missing-method" then
              enumResultRefusals := error :: enumResultRefusals
    | none => pure ()
    match IntegralMemberCallSyntax.admitResolved probe raw with
    | .ok evidence =>
        admitted := admitted + 1
        reports := jsonObject [
          ("ordinal", toJson ordinal),
          ("status", toJson "ADMIT"),
          ("method", toJson evidence.method.value),
          ("canonical_method", toJson evidence.canonicalMethod.value),
          ("receiver", toJson evidence.receiver.value),
          ("receiver_field", toJson (evidence.receiverField.map (·.value) |>.getD "")),
          ("receiver_base", toJson (evidence.receiverBase.map (·.value) |>.getD "")),
          ("receiver_field_name", toJson (evidence.receiverFieldName |>.getD "")),
          ("name", toJson evidence.name)] :: reports
    | .error reason =>
        let name := errorName reason
        refusals := name :: refusals
        if reason == .unsupportedArguments then
          argumentShapes := argumentShape raw :: argumentShapes
          match raw.field "inner" with
          | some (.array (_ :: arguments)) =>
              argumentTrees := (arguments.map rawTree).foldl (init := argumentTrees)
                (fun trees tree => tree :: trees)
              for (argument, ordinal) in arguments.zipIdx do
                if argument.text "kind" == some "IntegerLiteral" then
                  match IntegralMemberIntegerArgument.admit argument,
                      memberMethodHandle raw |>.bind (canonicalMethodHandle probe) with
                  | .ok evidence, some canonical => do
                      match IntegralMemberIntegerArgument.parameter probe canonical ordinal with
                      | .ok parameter =>
                          match IntegralMemberIntegerArgument.bindTo evidence parameter with
                          | .ok _ => integerArgumentBindings :=
                              (s!"{canonical.value}:{ordinal}") :: integerArgumentBindings
                          | .error error => integerArgumentRefusals :=
                              integerArgumentErrorName error :: integerArgumentRefusals
                      | .error error => integerArgumentRefusals :=
                          integerArgumentErrorName error :: integerArgumentRefusals
                      match IntegralMemberMethodProfile.admit probe canonical with
                      | .ok _ => do
                          integerMethodProfiles := canonical.value :: integerMethodProfiles
                      | .error error => do
                          integerMethodProfileRefusals :=
                          methodProfileErrorName error :: integerMethodProfileRefusals
                      match IntegralMemberMethodBody.admit probe canonical with
                      | .ok body => do
                          integerMethodBodies :=
                            (s!"{body.canonical.value}:{body.definition.value}") :: integerMethodBodies
                          match methodBodyObjectEvent probe body with
                          | some event => integerMethodObjectEvents :=
                              (s!"{body.canonical.value}:{event}") :: integerMethodObjectEvents
                          | none => integerMethodObjectRefusals :=
                              "missing-first-object-event" :: integerMethodObjectRefusals
                          for field in methodBodyThisFieldWrites probe body do
                            integerMethodThisFieldWrites :=
                              (s!"{body.canonical.value}:{field}") :: integerMethodThisFieldWrites
                          match methodBodyThisFieldWriteAccess probe body with
                          | some access =>
                              match IntegralMemberEnumProfile.admit probe access with
                              | .ok profile =>
                                  match IntegralMemberEnumRepresentation.withOracle profile .unsignedInt with
                                  | .ok representation =>
                                      match IntegralMemberEnumSetter.admit probe body.canonical representation with
                                      | .ok setter => integerMethodEnumSetterProfiles :=
                                          (s!"{setter.method.method.value}:{setter.fieldName}") ::
                                            integerMethodEnumSetterProfiles
                                      | .error error => integerMethodEnumSetterRefusals :=
                                          enumSetterErrorName error :: integerMethodEnumSetterRefusals
                                  | .error error => integerMethodEnumSetterRefusals :=
                                      ("representation:" ++ enumRepresentationErrorName error) ::
                                        integerMethodEnumSetterRefusals
                              | .error error => integerMethodEnumSetterRefusals :=
                                  ("enum:" ++ enumProfileErrorName error) :: integerMethodEnumSetterRefusals
                          | none => pure ()
                          match IntegralMemberThisFieldAccess.admit probe body with
                          | .ok access => do
                              integerMethodThisFields :=
                                (s!"{access.name}:{access.fieldType}:{access.receiverType}") ::
                                  integerMethodThisFields
                              match IntegralMemberEnumProfile.admit probe access with
                              | .ok profile => do
                                  integerMethodEnumProfiles :=
                                    (s!"{profile.name}:{profile.constantCount}:{profile.explicitValueCount}:" ++
                                      profile.underlyingType.getD "<absent>") :: integerMethodEnumProfiles
                                  match IntegralMemberEnumRepresentation.withOracle profile .unsignedInt with
                                  | .ok representation => integerMethodEnumRepresentations :=
                                  (s!"{representation.profile.name}:" ++
                                    IntegralMemberEnumRepresentation.underlyingName
                                      representation.underlying) ::
                                        integerMethodEnumRepresentations
                                  | .error error => integerMethodEnumRepresentationRefusals :=
                                      enumRepresentationErrorName error :: integerMethodEnumRepresentationRefusals
                              | .error error => integerMethodEnumProfileRefusals :=
                                  enumProfileErrorName error :: integerMethodEnumProfileRefusals
                          | .error error => do
                              integerMethodThisFieldRefusals :=
                                thisFieldErrorName error :: integerMethodThisFieldRefusals
                      | .error error => do
                          integerMethodBodyRefusals :=
                            methodBodyErrorName error :: integerMethodBodyRefusals
                  | .ok _, none => integerArgumentRefusals :=
                      "canonical-method-missing" :: integerArgumentRefusals
                  | .error error, _ => integerArgumentRefusals :=
                      integerArgumentErrorName error :: integerArgumentRefusals
          | _ => argumentTrees := "<malformed>" :: argumentTrees
        if reason == .unsupportedReceiver then
          receiverShapes := receiverShape raw :: receiverShapes
          receiverFamilies := receiverFamily raw :: receiverFamilies
        reports := jsonObject [
          ("ordinal", toJson ordinal),
          ("status", toJson "REFUSE"),
          ("reason", toJson name)] :: reports
  emit (jsonObject [
    ("format", toJson "cpp-member-call-census-1"),
    ("status", toJson "COMPLETE"),
    ("execution", toJson "not-attempted"),
    ("counting_basis", toJson "every retained CXXMemberCallExpr inner-tree occurrence"),
    ("call_sites", toJson calls.length),
    ("admitted", toJson admitted),
    ("refused", toJson refusals.length),
    ("first_refusals", counts refusals),
    ("unsupported_argument_shapes", counts argumentShapes),
    ("unsupported_argument_trees", counts argumentTrees),
    ("typed_integer_argument_bindings", counts integerArgumentBindings),
    ("typed_integer_argument_refusals", counts integerArgumentRefusals),
    ("typed_integer_method_profiles", counts integerMethodProfiles),
    ("typed_integer_method_profile_refusals", counts integerMethodProfileRefusals),
    ("typed_integer_method_bodies", counts integerMethodBodies),
    ("typed_integer_method_body_refusals", counts integerMethodBodyRefusals),
    ("typed_integer_method_object_events", counts integerMethodObjectEvents),
    ("typed_integer_method_object_refusals", counts integerMethodObjectRefusals),
    ("typed_integer_method_this_fields", counts integerMethodThisFields),
    ("typed_integer_method_this_field_refusals", counts integerMethodThisFieldRefusals),
    ("typed_integer_method_this_field_writes", counts integerMethodThisFieldWrites),
    ("typed_integer_method_enum_profiles", counts integerMethodEnumProfiles),
    ("typed_integer_method_enum_profile_refusals", counts integerMethodEnumProfileRefusals),
    ("typed_integer_method_enum_representations", counts integerMethodEnumRepresentations),
    ("typed_integer_method_enum_representation_refusals",
      counts integerMethodEnumRepresentationRefusals),
    ("typed_integer_method_enum_setter_profiles", counts integerMethodEnumSetterProfiles),
    ("typed_integer_method_enum_setter_refusals", counts integerMethodEnumSetterRefusals),
    ("enum_result_calls", counts enumResultCalls),
    ("enum_result_refusals", counts enumResultRefusals),
    ("enum_argument_shapes", counts enumArgumentShapes),
    ("enum_argument_refusals", counts enumArgumentRefusals),
    ("enum_argument_parameters", counts enumArgumentParameters),
    ("enum_argument_parameter_refusals", counts enumArgumentParameterRefusals),
    ("enum_argument_method_profiles", counts enumArgumentMethodProfiles),
    ("enum_argument_method_profile_refusals", counts enumArgumentMethodProfileRefusals),
    ("enum_argument_method_bodies", counts enumArgumentMethodBodies),
    ("enum_argument_method_body_refusals", counts enumArgumentMethodBodyRefusals),
    ("enum_argument_method_object_events", counts enumArgumentMethodObjectEvents),
    ("enum_argument_method_object_refusals", counts enumArgumentMethodObjectRefusals),
    ("enum_getter_profiles", counts enumGetterProfiles),
    ("enum_getter_refusals", counts enumGetterRefusals),
    ("unsupported_receiver_shapes", counts receiverShapes),
    ("unsupported_receiver_families", counts receiverFamilies),
    ("calls", toJson reports.reverse)])
  return 0

def main (arguments : List String) : IO UInt32 := do
  let [input] := arguments
    | IO.eprintln "usage: lake env lean --run extractors/cpp/census_member_calls.lean PROBE"; return 1
  try
    let before ← (System.FilePath.mk input).metadata
    unless before.type == .file do
      return ← refuse "input-io" "probe must be a regular file"
    if before.byteSize > 128 * 1024 * 1024 then
      return ← refuse "input-byte-bound" "probe exceeds 128 MiB runtime census bound"
    let bytes ← IO.FS.readBinFile input
    let after ← (System.FilePath.mk input).metadata
    unless before.byteSize == after.byteSize && before.modified == after.modified &&
        after.byteSize.toNat == bytes.size do
      return ← refuse "input-read" "probe changed while reading"
    let some contents := String.fromUTF8? bytes
      | return ← refuse "probe-format" "invalid UTF-8"
    let probe ← match parseDeclarationProbeString contents with
      | .ok probe => pure probe
      | .error reason => return ← refuse "probe-format" reason
    census probe
  catch error => refuse "input-io" error.toString
