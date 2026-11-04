import LeanModels.Cpp.StrictJson

namespace LeanModels.Cpp

structure FrontendHandle where
  value : String
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure FunctionShapeEvidence where
  definition : Bool
  bodyPresent : Bool
  defaulted : Bool
  deletedAsWritten : Bool
  skippedBody : Bool
  pendingBody : Bool
  definingAttribute : Bool
  lateParsed : Bool
  explicitlyDefaulted : Bool
  attributeCount : Nat
  ownBodyKind : Option String
  ownBodyOwner : Option FrontendHandle
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure DeclarationEvidenceRow where
  ordinal : Nat
  id : FrontendHandle
  kind : String
  canonical : FrontendHandle
  previous : Option FrontendHandle
  semanticContext : Option FrontendHandle
  lexicalContext : Option FrontendHandle
  implicit : Bool
  dependentContext : Bool
  owningModule : Option String
  functionShape : Option FunctionShapeEvidence
  raw : Raw
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure DeclarationProbe where
  ast : Raw
  metadata : Raw
  declarations : List DeclarationEvidenceRow
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def DeclarationProbe.functions (probe : DeclarationProbe) : List DeclarationEvidenceRow :=
  probe.declarations.filter fun row => row.functionShape.isSome

def evidenceField (raw : Raw) (name : String) : Except String Raw :=
  match raw.field name with
  | some value => .ok value
  | none => .error s!"missing evidence field: {name}"

def evidenceText (raw : Raw) (name : String) : Except String String := do
  match ← evidenceField raw name with
  | .string value => return value
  | _ => throw s!"evidence field {name}: expected string"

def evidenceBool (raw : Raw) (name : String) : Except String Bool := do
  match ← evidenceField raw name with
  | .bool value => return value
  | _ => throw s!"evidence field {name}: expected Boolean"

def evidenceArray (raw : Raw) (name : String) : Except String (List Raw) := do
  match ← evidenceField raw name with
  | .array values => return values
  | _ => throw s!"evidence field {name}: expected array"

def evidenceNullableText (raw : Raw) (name : String) : Except String (Option String) := do
  match ← evidenceField raw name with
  | .null => return none
  | .string value => return some value
  | _ => throw s!"evidence field {name}: expected string or explicit null"

def parseFrontendHandle (value : String) : Except String FrontendHandle := do
  let digits := match value.toList with
    | '0' :: 'x' :: rest => rest
    | _ => []
  unless !digits.isEmpty && digits.all (fun character =>
      character.isDigit || ('a' ≤ character && character ≤ 'f') ||
        ('A' ≤ character && character ≤ 'F')) &&
      value.toList.take 2 == ['0', 'x'] do
    throw s!"invalid artifact-local frontend handle: {value}"
  return {value}

def evidenceHandle (raw : Raw) (name : String) : Except String FrontendHandle := do
  parseFrontendHandle (← evidenceText raw name)

def evidenceNullableHandle (raw : Raw) (name : String) :
    Except String (Option FrontendHandle) := do
  match ← evidenceNullableText raw name with
  | none => return none
  | some value => return some (← parseFrontendHandle value)

def evidenceNat (raw : Raw) (name : String) : Except String Nat := do
  match ← evidenceField raw name with
  | .number token =>
      match token.toInt? with
      | some value =>
          if value < 0 then throw s!"evidence field {name}: expected nonnegative integer"
          else return value.toNat
      | none => throw s!"evidence field {name}: expected integer token"
  | _ => throw s!"evidence field {name}: expected integer token"

def requireEvidenceText (raw : Raw) (name expected : String) : Except String Unit := do
  let actual ← evidenceText raw name
  unless actual == expected do
    throw s!"evidence field {name}: expected '{expected}', got '{actual}'"

def evidenceApiBool (raw : Raw) (name api : String) : Except String Bool := do
  requireEvidenceText raw (name ++ "_api") api
  evidenceBool raw name

def parseFunctionShapeEvidence (raw : Raw) : Except String FunctionShapeEvidence := do
  requireEvidenceText raw "definition_api" "FunctionDecl.isThisDeclarationADefinition"
  let definition ← evidenceBool raw "definition"
  let bodyPresent ← evidenceBool raw "body_present"
  let defaulted ← evidenceBool raw "defaulted"
  let deletedAsWritten ← evidenceBool raw "deleted_as_written"
  let skippedBody ← evidenceApiBool raw "function_has_skipped_body" "FunctionDecl.hasSkippedBody"
  let pendingBody ← evidenceApiBool raw "function_will_have_body" "FunctionDecl.willHaveBody"
  let definingAttribute ← evidenceApiBool raw "function_has_defining_attr" "FunctionDecl.hasDefiningAttr"
  let lateParsed ← evidenceApiBool raw "function_late_template_parsed" "FunctionDecl.isLateTemplateParsed"
  let explicitlyDefaulted ← evidenceApiBool raw "function_explicitly_defaulted" "FunctionDecl.isExplicitlyDefaulted"
  requireEvidenceText raw "function_attribute_count_api" "Decl.hasAttrs/Decl.getAttrs.size"
  let attributeCount ← evidenceNat raw "function_attribute_count"
  requireEvidenceText raw "own_body_api" "FunctionDecl.getBody"
  let ownBodyKind ← evidenceNullableText raw "own_body_kind"
  if ownBodyKind == some "" then throw "own_body_kind: expected nonempty string or explicit null"
  let ownBodyOwner ← evidenceNullableHandle raw "own_body_owner"
  return {definition, bodyPresent, defaulted, deletedAsWritten, skippedBody, pendingBody,
          definingAttribute, lateParsed, explicitlyDefaulted, attributeCount,
          ownBodyKind, ownBodyOwner}

def parseDeclarationEvidenceRow (ordinal : Nat) (raw : Raw) :
    Except String DeclarationEvidenceRow := do
  let id ← evidenceHandle raw "id"
  let kind ← evidenceText raw "kind"
  unless kind.endsWith "Decl" do throw "metadata kind must be a declaration family"
  let canonical ← evidenceHandle raw "canonical"
  let previous ← evidenceNullableHandle raw "previous"
  let semanticContext ← evidenceNullableHandle raw "semantic_context"
  let lexicalContext ← evidenceNullableHandle raw "lexical_context"
  let implicit ← evidenceBool raw "implicit"
  let dependentContext ← evidenceBool raw "dependent_context"
  let owningModule ← evidenceNullableText raw "owning_module"
  let functionShape ← if kind == "FunctionDecl" then
      pure (some (← parseFunctionShapeEvidence raw)) else pure none
  return {ordinal, id, kind, canonical, previous, semanticContext, lexicalContext,
          implicit, dependentContext, owningModule, functionShape, raw}

def validateProbeMetadata (metadata : Raw) : Except String Unit := do
  requireEvidenceText metadata "schema_version" "cpp-canonical-probe-0.3"
  requireEvidenceText metadata "compiled_frontend" "21.1.8"
  requireEvidenceText metadata "llvm_headers" "21.1.8"
  let runtime ← evidenceText metadata "runtime_frontend"
  unless runtime == "clang version 21.1.8" || runtime.startsWith "clang version 21.1.8 " do
    throw "unsupported runtime frontend"

def parseDeclarationProbe (raw : Raw) : Except String DeclarationProbe := do
  validateStrictRaw raw
  let ast ← evidenceField raw "ast"
  requireEvidenceText ast "kind" "TranslationUnitDecl"
  let _ ← evidenceHandle ast "id"
  let metadata ← evidenceField raw "metadata"
  validateProbeMetadata metadata
  let rows ← evidenceArray metadata "declarations"
  let declarations ← rows.zipIdx.mapM fun (row, ordinal) =>
    parseDeclarationEvidenceRow ordinal row
  return {ast, metadata, declarations}

def parseDeclarationProbeString (contents : String) : Except String DeclarationProbe := do
  parseDeclarationProbe (← parseStrictRawString contents)

end LeanModels.Cpp
