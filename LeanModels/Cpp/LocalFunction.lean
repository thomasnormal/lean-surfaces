import LeanModels.Cpp.Identity

namespace LeanModels.Cpp

def Raw.atPath (raw : Raw) (path : List Nat) : Option Raw :=
  match path with
  | [] => some raw
  | index :: rest => do
      let children ← (raw.field "inner").bind Raw.array?
      let child ← children[index]?
      child.atPath rest

inductive LocalFunctionForm where
  | declaration
  | deleted
  | compound (body : Raw)
  | functionTry (body : Raw)
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def LocalFunctionForm.definesEntity : LocalFunctionForm → Bool
  | .declaration => false
  | _ => true

structure LocalFunctionDeclaration where
  occurrence : Declaration
  parameters : List Raw
  form : LocalFunctionForm
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def cppIdentifier (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest =>
      (first.isAlpha && first.toNat < 128 || first == '_') &&
        rest.all (fun character =>
          character.toNat < 128 && (character.isAlphanum || character == '_'))

def localFunctionRow (probe : DeclarationProbe) (id : String) :
    Except String DeclarationEvidenceRow := do
  match probe.declarations.filter (fun row => row.id.value == id) with
  | [] => throw "local function: missing declaration metadata"
  | row :: rest =>
      unless rest.all (fun other => other.raw == row.raw) do
        throw "local function: conflicting declaration metadata"
      if row.implicit || row.dependentContext || row.owningModule.isSome then
        throw "local function: implicit, dependent or module declaration"
      return row

def optionalSourceBool (raw : Raw) (name : String) : Except String Bool :=
  match raw.field name with
  | none => .ok false
  | some (.bool value) => .ok value
  | some _ => .error s!"local function: malformed source flag {name}"

def localFunctionScope (probe : DeclarationProbe) (handle : FrontendHandle)
    (allowRecord : Bool := false) :
    Except String Unit := do
  let row ← localFunctionRow probe handle.value
  if row.kind == "TranslationUnitDecl" then return
  if allowRecord && row.kind == "CXXRecordDecl" then
    unless cppIdentifier (← evidenceText row.raw "name") do
      throw "local function: unsupported record name"
    if (← evidenceBool row.raw "injected_class_name") then
      throw "local function: injected class scope"
    requireEvidenceText row.raw "described_template_api" "CXXRecordDecl.getDescribedClassTemplate"
    unless (← evidenceNullableHandle row.raw "described_template").isNone &&
        (← evidenceNat row.raw "template_specialization_kind") == 0 do
      throw "local function: template record scope"
    return
  unless row.kind == "NamespaceDecl" do
    throw s!"local function: unsupported scope {row.kind}"
  unless cppIdentifier (← evidenceText row.raw "name") do
    throw "local function: unsupported namespace name"
  if (← evidenceBool row.raw "inline_namespace") ||
      (← evidenceBool row.raw "anonymous_namespace") then
    throw "local function: inline or anonymous namespace"

def localFunctionScopeSource (artifact : Artifact) (probe : DeclarationProbe)
    (handle : FrontendHandle) (allowRecord : Bool := false) : Except String Unit := do
  localFunctionScope probe handle allowRecord
  let row ← localFunctionRow probe handle.value
  if row.kind == "TranslationUnitDecl" then return
  let occurrences := artifact.declarationsById handle.value
  if occurrences.isEmpty then throw "local function: namespace source is absent"
  occurrences.forM fun occurrence => do
    let some raw := artifact.ast.atPath occurrence.path
      | throw "local function: namespace occurrence is absent"
    unless raw.text "kind" == some row.kind && raw.text "name" == row.raw.text "name" do
      throw "local function: namespace source disagrees with metadata"
    if (← optionalSourceBool raw "isInline") || (← optionalSourceBool raw "isImplicit") then
      throw "local function: inline or implicit namespace source"

def localFunctionChildren (raw : Raw) : Except String (List Raw × Option Raw) := do
  let children ← match raw.field "inner" with
    | none => pure []
    | some (.array children) => pure children
    | some _ => throw "local function: malformed source children"
  go children []
where
  go (children parameters : List Raw) : Except String (List Raw × Option Raw) := do
    match children with
    | [] => return (parameters.reverse, none)
    | child :: rest =>
        if child.text "kind" == some "ParmVarDecl" then
          go rest (child :: parameters)
        else if rest.isEmpty &&
            (child.text "kind" == some "CompoundStmt" || child.text "kind" == some "CXXTryStmt") then
          return (parameters.reverse, some child)
        else
          throw "local function: unsupported source child or body order"

def admitLocalFunctionDeclaration (probe : DeclarationProbe) (path : List Nat) :
    Except String LocalFunctionDeclaration := do
  let artifact : Artifact := {
    sourceFile := "", sourceSha256 := "", frontend := .object [], dependencies := []
    ast := probe.ast }
  let some raw := probe.ast.atPath path
    | throw "local function: source occurrence is absent"
  let some id := raw.text "id" | throw "local function: source handle is absent"
  let isMethod := raw.text "kind" == some "CXXMethodDecl"
  unless raw.text "kind" == some "FunctionDecl" || isMethod do
    throw "local function: requires FunctionDecl or static CXXMethodDecl"
  let row ← localFunctionRow probe id
  unless some row.kind == raw.text "kind" do
    throw "local function: source and metadata families disagree"
  let shape ← if isMethod then
      requireEvidenceText row.raw "method_static_api" "CXXMethodDecl.isStatic"
      unless (← evidenceBool row.raw "method_static") do
        throw "local function: instance method requires object semantics"
      parseFunctionShapeEvidence row.raw
    else match row.functionShape with
      | some shape => pure shape
      | none => throw "local function: missing shape evidence"
  let name ← evidenceText raw "name"
  unless cppIdentifier name && row.raw.text "name" == some name do
    throw "local function: unsupported or inconsistent function name"
  requireEvidenceText row.raw "function_templated_kind_api" "FunctionDecl.getTemplatedKind"
  requireEvidenceText row.raw "template_specialization_kind_api" "FunctionDecl.getTemplateSpecializationKind"
  unless (← evidenceNat row.raw "function_templated_kind") == 0 &&
      (← evidenceNat row.raw "template_specialization_kind") == 0 do
    throw "local function: templates or specializations"
  if shape.skippedBody || shape.pendingBody || shape.lateParsed then
    throw "local function: skipped, pending or late-parsed body"
  if shape.defaulted || shape.explicitlyDefaulted then
    throw "local function: defaulted function"
  if shape.definingAttribute || shape.attributeCount != 0 then
    throw "local function: attributed declaration"
  if (← optionalSourceBool raw "isImplicit") || (raw.field "explicitlyDefaulted").isSome then
    throw "local function: implicit or defaulted source form"
  let some lexical := row.lexicalContext | throw "local function: missing lexical scope"
  let some semantic := row.semanticContext | throw "local function: missing semantic scope"
  localFunctionScope probe lexical isMethod
  localFunctionScope probe semantic isMethod
  let some occurrence := artifact.declarationAtPath path
    | throw "local function: source declaration is absent"
  let lexicalChain ← lexicalContextChainEvidence artifact probe occurrence
  let semanticChain ← semanticContextChainEvidence artifact probe occurrence
  unless lexicalChain.map (·.value) == occurrence.lexicalParents.reverse do
    throw "local function: lexical scope disagrees with source ancestry"
  unless semantic.value == occurrence.semanticParent.getD lexical.value do
    throw "local function: semantic scope disagrees with source occurrence"
  lexicalChain.forM (fun handle => localFunctionScopeSource artifact probe handle isMethod)
  semanticChain.forM (fun handle => localFunctionScopeSource artifact probe handle isMethod)
  if isMethod then
    unless (← localFunctionRow probe semantic.value).kind == "CXXRecordDecl" do
      throw "local function: static method requires a record semantic scope"
    let root ← canonicalRootEvidence probe occurrence
    let predecessors ← canonicalPredecessorChainEvidence probe occurrence
    predecessors.forM fun handle => do
      let predecessor ← localFunctionRow probe handle.value
      requireEvidenceText predecessor.raw "method_static_api" "CXXMethodDecl.isStatic"
      unless (← evidenceBool predecessor.raw "method_static") &&
          predecessor.semanticContext == some semantic do
        throw "local function: inconsistent static method redeclaration"
    unless (artifact.declarationsById root.value).any (fun candidate =>
        candidate.kind == "CXXMethodDecl" && candidate.name == some name &&
          (artifact.ast.atPath candidate.path).any (fun source =>
            source.text "storageClass" == some "static")) do
      throw "local function: canonical static declaration is absent from AST"
  let (parameters, body) ← localFunctionChildren raw
  let deleted ← optionalSourceBool raw "explicitlyDeleted"
  unless deleted == shape.deletedAsWritten do
    throw "local function: deletion evidence disagrees with source form"
  let form ← match body with
    | none =>
        if shape.bodyPresent || shape.ownBodyKind.isSome || shape.ownBodyOwner.isSome then
          throw "local function: body evidence disagrees with bodyless source form"
        pure (if deleted then LocalFunctionForm.deleted else .declaration)
    | some body =>
        unless !deleted && shape.bodyPresent && shape.ownBodyOwner == some row.id &&
            shape.ownBodyKind == body.text "kind" do
          throw "local function: body evidence disagrees with owned source body"
        if body.text "kind" == some "CompoundStmt" then
          pure (LocalFunctionForm.compound body)
        else pure (LocalFunctionForm.functionTry body)
  unless shape.definition == form.definesEntity do
    throw "local function: definition getter disagrees with source classification"
  return {occurrence, parameters, form}

end LeanModels.Cpp
