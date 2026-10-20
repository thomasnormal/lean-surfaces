import LeanModels.Cpp.LocalFunction
import LeanModels.Cpp.TypeEvidence

namespace LeanModels.Cpp

structure IntegralRecordField where
  declaration : FrontendHandle
  name : String
  type : CppTypeEvidence
  isMutable : Bool
  deriving Repr, BEq, Inhabited

structure IntegralRecordSchema where
  declaration : FrontendHandle
  name : String
  fields : List IntegralRecordField
  deriving Repr, BEq, Inhabited

/-- Integral identity and top-level constness; volatile and other families refuse. -/
def recordIntegralKind : CppTypeEvidence → Option (CppIntType × Bool)
  | .builtin kind => some (kind, false)
  | .qualified isConst false base =>
      (recordIntegralKind base).map fun (kind, constant) => (kind, constant || isConst)
  | _ => none

def IntegralRecordSchema.valid (schema : IntegralRecordSchema) : Bool :=
  cppIdentifier schema.name && schema.fields.all (fun field =>
    cppIdentifier field.name && field.declaration != schema.declaration &&
      (recordIntegralKind field.type).any (fun (_, constant) => !field.isMutable || !constant)) &&
    (schema.fields.map (·.declaration)).eraseDups.length == schema.fields.length &&
    (schema.fields.map (·.name)).eraseDups.length == schema.fields.length

private def children (raw : Raw) : Except String (List Raw) :=
  match raw.field "inner" with
  | none => pure []
  | some (.array values) => pure values
  | _ => throw "record schema: malformed children"

private def fieldType (types : List TypeEvidenceRow) (handle : FrontendHandle) :
    Except String CppTypeEvidence := do
  let row :: rest := types.filter (·.occurrence == handle)
    | throw "record schema: missing structured field type"
  unless row.canonical == handle && rest.all (·.type == row.type) do
    throw "record schema: inconsistent field type evidence"
  pure row.type

/-- Already validated whole-probe types; every member is retained in exact order. -/
def admitIntegralRecordSchemaWithTypes (probe : DeclarationProbe)
    (types : List TypeEvidenceRow) (path : List Nat) : Except String IntegralRecordSchema := do
  let artifact : Artifact := {
    sourceFile := "", sourceSha256 := "", frontend := .null,
    dependencies := [], ast := probe.ast}
  let some raw := probe.ast.atPath path | throw "record schema: absent occurrence"
  unless raw.text "kind" == some "CXXRecordDecl" do throw "record schema: requires CXXRecordDecl"
  let row ← localFunctionRow probe (← evidenceText raw "id")
  unless row.kind == "CXXRecordDecl" do throw "record schema: declaration family mismatch"
  localFunctionScope probe row.id true
  requireEvidenceText row.raw "record_shape_api" "CXXRecordDecl aggregate member shape v1"
  unless (← evidenceBool row.raw "record_complete") &&
      (← optionalSourceBool raw "completeDefinition") do throw "record schema: incomplete definition"
  unless !(← evidenceBool row.raw "record_union") &&
      (← evidenceBool row.raw "record_aggregate") &&
      (← evidenceNat row.raw "record_base_count") == 0 &&
      (← evidenceBool row.raw "record_trivial_destructor") &&
      !(← evidenceBool row.raw "record_user_destructor") &&
      (← evidenceNat row.raw "record_attribute_count") == 0 do
    throw "record schema: requires an unattributed non-union aggregate without bases or user-declared/nontrivial destruction"
  unless raw.text "tagUsed" == some "struct" || raw.text "tagUsed" == some "class" do
    throw "record schema: unsupported source record tag"
  let name ← evidenceText raw "name"
  unless row.raw.text "name" == some name do throw "record schema: inconsistent record name"
  let some occurrence := artifact.declarationAtPath path | throw "record schema: missing source declaration"
  let root ← canonicalRootEvidence probe occurrence
  let _ ← canonicalPredecessorChainEvidence probe occurrence
  let lexical ← lexicalContextChainEvidence artifact probe occurrence
  let semantic ← semanticContextChainEvidence artifact probe occurrence
  unless lexical.map (·.value) == occurrence.lexicalParents.reverse do
    throw "record schema: inconsistent lexical ancestry"
  lexical.forM (fun context => localFunctionScopeSource artifact probe context true)
  semantic.forM (fun context => localFunctionScopeSource artifact probe context true)
  let raws := (← children raw).filter (·.text "kind" == some "FieldDecl")
  unless raws.length == (← evidenceNat row.raw "record_field_count") do
    throw "record schema: incomplete field census"
  let mut fields := []
  for (field, index) in raws.zipIdx do
    let handle ← evidenceHandle field "id"
    let metadata ← localFunctionRow probe handle.value
    unless metadata.kind == "FieldDecl" && metadata.canonical == handle &&
        metadata.semanticContext == some row.id && metadata.lexicalContext == some row.id do
      throw "record schema: field owner or identity mismatch"
    requireEvidenceText metadata.raw "field_shape_api" "FieldDecl member shape v1"
    unless (← evidenceHandle metadata.raw "field_parent") == row.id &&
        (← evidenceNat metadata.raw "field_index") == index do
      throw "record schema: field order or parent mismatch"
    unless !(← evidenceBool metadata.raw "field_bitfield") &&
        !(← evidenceBool metadata.raw "field_initializer") &&
        (← evidenceNat metadata.raw "field_attribute_count") == 0 &&
        (← children field).isEmpty do
      throw "record schema: bit-field, initializer or field attribute"
    let isMutable ← evidenceBool metadata.raw "field_mutable"
    unless isMutable == (← optionalSourceBool field "mutable") &&
        !(← optionalSourceBool field "isBitfield") &&
        !(← optionalSourceBool field "hasInClassInitializer") do
      throw "record schema: field source flags disagree"
    let fieldName ← evidenceText field "name"
    unless metadata.raw.text "name" == some fieldName do throw "record schema: inconsistent field name"
    fields := fields ++ [{
      declaration := handle, name := fieldName,
      type := ← fieldType types handle, isMutable}]
  let schema := {declaration := root, name, fields : IntegralRecordSchema}
  unless schema.valid do throw "record schema: unsupported or duplicate integral field"
  pure schema

def admitIntegralRecordSchema (probe : DeclarationProbe) (path : List Nat) :
    Except String IntegralRecordSchema := do
  let types ← parseValidatedTypeEvidence probe
  admitIntegralRecordSchemaWithTypes probe types path

end LeanModels.Cpp
