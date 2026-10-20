import LeanModels.Cpp.ExpressionEvidence

namespace LeanModels.Cpp

inductive CppVariableStorageClass where
  | none_ | extern_ | static_ | privateExtern | auto_ | register_
  deriving Repr, BEq, Inhabited

inductive CppVariableStorageDuration where
  | automatic | thread | static_
  deriving Repr, BEq, Inhabited

inductive CppVariableTLS where
  | none_ | static_ | dynamic_
  deriving Repr, BEq, Inhabited

inductive CppVariableInitStyle where
  | c | call | list | parenList
  deriving Repr, BEq, Inhabited

abbrev CppInitializerExpressionType := CppExpressionTypeEvidence

structure CppVariableInitializerEvidence where
  occurrence : FrontendHandle
  kind : String
  sourceType : CppTypeEvidence
  type : CppTypeEvidence
  expressionTypes : List CppInitializerExpressionType := []
  deriving Repr, BEq, Inhabited

/-- Frontend observations only. This is not an automatic-local admission judgment. -/
structure CppVariableEvidence where
  ordinal : Nat
  occurrence : FrontendHandle
  canonical : FrontendHandle
  kind : String
  isLocal : Bool
  localOrParameter : Bool
  storageClass : CppVariableStorageClass
  storageDuration : CppVariableStorageDuration
  tls : CppVariableTLS
  initStyle : CppVariableInitStyle
  initializer : Option CppVariableInitializerEvidence
  isConstexpr : Bool
  attributeCount : Nat
  deriving Repr, BEq, Inhabited

private def variableApi := "Clang::VarDecl storage and initializer projection v1"

private def storageClass (name : String) : Except String CppVariableStorageClass :=
  match name with
  | "none" => .ok .none_
  | "extern" => .ok .extern_
  | "static" => .ok .static_
  | "private-extern" => .ok .privateExtern
  | "auto" => .ok .auto_
  | "register" => .ok .register_
  | _ => .error "variable evidence: unknown storage class"

private def storageDuration (name : String) : Except String CppVariableStorageDuration :=
  match name with
  | "automatic" => .ok .automatic
  | "thread" => .ok .thread
  | "static" => .ok .static_
  | _ => .error "variable evidence: unsupported VarDecl storage duration"

private def tlsKind (name : String) : Except String CppVariableTLS :=
  match name with
  | "none" => .ok .none_
  | "static" => .ok .static_
  | "dynamic" => .ok .dynamic_
  | _ => .error "variable evidence: unknown TLS kind"

private def initStyle (name : String) : Except String CppVariableInitStyle :=
  match name with
  | "c" => .ok .c
  | "call" => .ok .call
  | "list" => .ok .list
  | "paren-list" => .ok .parenList
  | _ => .error "variable evidence: unknown initialization style"

private def CppVariableInitStyle.token : CppVariableInitStyle → String
  | .c => "c" | .call => "call" | .list => "list" | .parenList => "paren-list"

private def parseInitializerTypes (raw : Raw) :
    Except String (List CppInitializerExpressionType) := do
  match raw.field "expression_types_api", raw.field "expression_types" with
  | none, none => pure []
  | some (.string "Clang::Expr initializer type projection v1"), some (.array rows) =>
      unless !rows.isEmpty do throw "initializer expression types: empty supplement"
      rows.mapM fun row => return {
        occurrence := ← evidenceHandle row "occurrence"
        kind := ← evidenceText row "kind"
        type := ← parseCppTypeEvidence (← evidenceField row "type") }
  | _, _ => throw "initializer expression types: missing or unsupported supplement"

private def parseVariableRow (ordinal : Nat) (raw : Raw) :
    Except String CppVariableEvidence := do
  requireEvidenceText raw "variable_api" variableApi
  let kind ← evidenceText raw "kind"
  unless ["VarDecl", "ParmVarDecl", "ImplicitParamDecl", "DecompositionDecl",
      "VarTemplateSpecializationDecl", "VarTemplatePartialSpecializationDecl"].contains kind do
    throw "variable evidence: kind is not a VarDecl family"
  let hasInitializer ← evidenceBool raw "has_initializer"
  let initializer ← match ← evidenceField raw "initializer" with
    | .null => pure none
    | value@(.object _) => pure (some {
        occurrence := ← evidenceHandle value "occurrence"
        kind := ← evidenceText value "kind"
        sourceType := ← parseCppTypeEvidence (← evidenceField value "source")
        type := ← parseCppTypeEvidence (← evidenceField value "type")
        expressionTypes := ← parseInitializerTypes value
      } : Option CppVariableInitializerEvidence)
    | _ => throw "variable evidence: initializer requires object or explicit null"
  unless hasInitializer == initializer.isSome do
    throw "variable evidence: has_initializer disagrees with initializer"
  return {
    ordinal, kind
    occurrence := ← evidenceHandle raw "occurrence"
    canonical := ← evidenceHandle raw "canonical"
    isLocal := ← evidenceBool raw "local"
    localOrParameter := ← evidenceBool raw "local_or_parameter"
    storageClass := ← storageClass (← evidenceText raw "storage_class")
    storageDuration := ← storageDuration (← evidenceText raw "storage_duration")
    tls := ← tlsKind (← evidenceText raw "tls")
    initStyle := ← initStyle (← evidenceText raw "init_style")
    initializer
    isConstexpr := ← evidenceBool raw "constexpr"
    attributeCount := ← evidenceNat raw "attribute_count"
  }

def parseVariableEvidenceRows (raw : Raw) : Except String (List CppVariableEvidence) := do
  let .array values := raw | throw "variable evidence: expected array"
  values.zipIdx.mapM fun (value, ordinal) => parseVariableRow ordinal value

mutual
  /-- Walk the AST's root/inner tree; reference and type stubs cannot witness a row. -/
  private def variableAstNodes : Raw → List Raw
    | node@(.object fields) => node :: variableAstFields fields
    | _ => []

  private def variableAstFields : List (String × Raw) → List Raw
    | [] => []
    | (name, value) :: rest =>
        (if name == "inner" then
          match value with
          | .array values => variableAstValues values
          | _ => []
        else []) ++ variableAstFields rest

  private def variableAstValues : List Raw → List Raw
    | [] => []
    | value :: rest => variableAstNodes value ++ variableAstValues rest
end

private def astFlag (node : Raw) (field : String) : Except String Bool :=
  match node.field field with
  | none => .ok false
  | some (.bool value) => .ok value
  | _ => .error s!"variable AST field {field}: expected Boolean"

private def validateVariableNode (probe : DeclarationProbe) (row : CppVariableEvidence)
    (node : Raw) : Except String Unit := do
  unless node.text "kind" == some row.kind do
    throw "variable evidence kind disagrees with AST"
  let expectedStorage := match row.storageClass with
    | .none_ => none | .extern_ => some "extern" | .static_ => some "static"
    | .privateExtern => some "__private_extern__" | .auto_ => some "auto"
    | .register_ => some "register"
  unless node.field "storageClass" == expectedStorage.map Raw.string do
    throw "variable storage class disagrees with AST"
  let expectedTLS := match row.tls with
    | .none_ => none | .static_ => some "static" | .dynamic_ => some "dynamic"
  unless node.field "tls" == expectedTLS.map Raw.string do
    throw "variable TLS kind disagrees with AST"
  unless (← astFlag node "constexpr") == row.isConstexpr do
    throw "variable constexpr flag disagrees with AST"
  let children ← match node.field "inner" with
    | none => pure []
    | some (.array children) => pure children
    | _ => throw "variable AST inner field is not an array"
  let attributes := children.filter (fun child =>
    (child.text "kind").any (·.endsWith "Attr"))
  unless attributes.length == row.attributeCount do
    throw "variable attribute count disagrees with AST"
  let values := children.filter (fun child =>
    !(child.text "kind").any (fun kind => kind.endsWith "Attr" || ["FullComment", "TemplateArgument", "BindingDecl"].contains kind))
  match row.initializer with
  | none =>
      unless node.field "init" == none && values.isEmpty && row.initStyle == .c do
        throw "variable without initializer disagrees with AST"
  | some initializer =>
      unless node.text "init" == some row.initStyle.token do
        throw "variable initialization style disagrees with AST"
      let [value] := values
        | throw "variable AST requires exactly one initializer child"
      unless value.text "id" == some initializer.occurrence.value &&
          value.text "kind" == some initializer.kind do
        throw "variable initializer identity/kind disagrees with AST"
      unless initializer.sourceType.referencesKnown probe.declarations &&
          initializer.type.referencesKnown probe.declarations do
        throw "variable initializer type references absent declaration"
      let nodes := variableAstNodes value
      for expression in initializer.expressionTypes do
        unless expression.type.referencesKnown probe.declarations do
          throw "initializer expression type references absent declaration"
        let matchingRows := nodes.filter (·.text "id" == some expression.occurrence.value)
        unless !matchingRows.isEmpty && matchingRows.all (·.text "kind" == some expression.kind) do
          throw "initializer expression type occurrence/kind disagrees with subtree"
        unless initializer.expressionTypes.all (fun other =>
            other.occurrence != expression.occurrence || other == expression) do
          throw "conflicting initializer expression types"
      unless initializer.expressionTypes.isEmpty || initializer.expressionTypes.any (fun row =>
          row.occurrence == initializer.occurrence && row.kind == initializer.kind &&
            row.type == initializer.type) do
        throw "initializer root type disagrees with expression types"

def validateVariableEvidence (probe : DeclarationProbe) (rows : List CppVariableEvidence) :
    Except String Unit := do
  let types ← parseValidatedTypeEvidence probe
  let nodes := variableAstNodes probe.ast
  let rec validate (remaining seen : List CppVariableEvidence) : Except String Unit := do
    match remaining with
    | [] => pure ()
    | row :: rest =>
        let declarations := probe.declarations.filter (·.id == row.occurrence)
        unless !declarations.isEmpty && declarations.all (fun declaration =>
            declaration.kind == row.kind && declaration.canonical == row.canonical) do
          throw "variable occurrence/canonical/kind disagrees with declaration metadata"
        unless (typeEvidenceFor types row.occurrence).isSome do
          throw "variable occurrence lacks structured type evidence"
        let occurrences :=  nodes.filter (·.text "id" == some row.occurrence.value)
        if occurrences.isEmpty then throw "variable evidence occurrence is absent from AST inner tree"
        for node in occurrences do validateVariableNode probe row node
        if row.isLocal && !row.localOrParameter then
          throw "variable local status is inconsistent"
        if row.kind == "ParmVarDecl" && (row.isLocal || !row.localOrParameter) then
          throw "variable parameter status is inconsistent"
        if row.kind != "ParmVarDecl" && row.isLocal != row.localOrParameter then
          throw "variable local/parameter status is inconsistent"
        unless (row.storageDuration == .thread) == (row.tls != .none_) do
          throw "variable storage duration disagrees with TLS kind"
        let expectedDuration : CppVariableStorageDuration := if row.tls != .none_ then .thread
          else if row.localOrParameter && [.none_, .auto_, .register_].contains row.storageClass
            then .automatic else .static_
        unless row.kind == "ImplicitParamDecl" || row.storageDuration == expectedDuration do
          throw "variable storage duration disagrees with role/storage/TLS"
        if seen.any (fun prior => prior.occurrence == row.occurrence &&
            {prior with ordinal := 0} != {row with ordinal := 0}) then
          throw "conflicting repeated variable evidence"
        validate rest (row :: seen)
  validate rows []

def parseValidatedVariableEvidence (probe : DeclarationProbe) :
    Except String (List CppVariableEvidence) := do
  requireEvidenceText probe.metadata "variable_evidence_api" variableApi
  let rows ← parseVariableEvidenceRows (← evidenceField probe.metadata "variable_evidence")
  validateVariableEvidence probe rows
  pure rows

end LeanModels.Cpp
