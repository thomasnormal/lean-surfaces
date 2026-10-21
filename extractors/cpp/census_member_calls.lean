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
  let mut receiverShapes : List String := []
  let mut receiverFamilies : List String := []
  let mut reports : List Json := []
  for (raw, ordinal) in calls.zipIdx do
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
