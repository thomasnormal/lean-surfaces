import LeanModels.Cpp.MemberGetters

namespace LeanModels.Cpp

/-- A class description, not a constructor or an integral aggregate schema.
Every listed base is nonvirtual; field handles retain ownership, not values. -/
structure ClassBaseSpec where
  target : FrontendHandle
  access : String
  writtenAccess : String
  deriving Repr, BEq, Inhabited

structure ClassShape where
  declaration : FrontendHandle
  isAbstract : Bool
  bases : List ClassBaseSpec
  fields : List FrontendHandle
  deriving Repr, BEq, Inhabited

structure ClassSubobjectSlot where
  path : List Nat
  declaration : FrontendHandle
  deriving Repr, BEq, Inhabited

structure ClassHierarchy where
  root : FrontendHandle
  classes : List ClassShape
  deriving Repr, BEq, Inhabited

namespace ClassHierarchy

private def expand : Nat → ClassHierarchy → FrontendHandle → List FrontendHandle →
    List Nat → Except String (List ClassSubobjectSlot)
  | 0, _, _, _, _ => .error "class hierarchy: cyclic or exhausted base graph"
  | fuel + 1, hierarchy, declaration, active, path => do
      if active.contains declaration then throw "class hierarchy: cyclic base graph"
      let some shape := hierarchy.classes.find? (·.declaration == declaration)
        | throw "class hierarchy: absent base description"
      let mut slots := [{path, declaration}]
      for (base, index) in shape.bases.zipIdx do
        slots := slots ++ (← expand fuel hierarchy base.target (declaration :: active) (path ++ [index]))
      pure slots

/-- Expand occurrences, preserving both copies of a repeated nonvirtual base. -/
def slots (hierarchy : ClassHierarchy) : Except String (List ClassSubobjectSlot) := do
  let names := hierarchy.classes.map (·.declaration)
  unless !names.isEmpty && names.eraseDups.length == names.length do
    throw "class hierarchy: duplicate or absent class descriptions"
  let fields := hierarchy.classes.flatMap (·.fields)
  unless fields.eraseDups.length == fields.length &&
      fields.all (fun field => !names.contains field) &&
      hierarchy.classes.all (fun shape =>
        (shape.bases.map (·.target)).eraseDups.length == shape.bases.length) do
    throw "class hierarchy: inconsistent field or direct-base identities"
  let some root := hierarchy.classes.find? (·.declaration == hierarchy.root)
    | throw "class hierarchy: absent complete root"
  if root.isAbstract then throw "class hierarchy: abstract complete object"
  let result ← expand (hierarchy.classes.length + 1) hierarchy hierarchy.root [] []
  unless names.all (fun name => result.any (·.declaration == name)) do
    throw "class hierarchy: unused class description"
  pure result

end ClassHierarchy

namespace ClassHierarchyAdmission

private def children (raw : Raw) : Except String (List Raw) :=
  match raw.field "inner" with
  | none => .ok []
  | some (.array values) => .ok values
  | _ => .error "class hierarchy: malformed source children"

private def source (artifact : Artifact) (probe : DeclarationProbe)
    (canonical : FrontendHandle) : Except String (Declaration × Raw × DeclarationEvidenceRow) := do
  let possible := probe.declarations.filter (fun row => row.canonical == canonical &&
    row.kind == "CXXRecordDecl" && row.raw.field "record_complete" == some (.bool true))
  let candidates ← (artifact.declarations.filter (fun declaration =>
      declaration.kind == "CXXRecordDecl" && possible.any (·.id.value == declaration.id))).filterMapM fun declaration => do
    let row ← localFunctionRow probe declaration.id
    if row.canonical == canonical && row.raw.field "record_complete" == some (.bool true) then
      let some raw := artifact.ast.atPath declaration.path
        | throw "class hierarchy: absent source"
      pure (some (declaration, raw, row))
    else pure none
  let first :: rest := candidates | throw "class hierarchy: missing complete source definition"
  unless rest.all (fun other => other.1.id == first.1.id && other.2.1 == first.2.1) do
    throw "class hierarchy: conflicting complete source definitions"
  pure first

private def shape (artifact : Artifact) (probe : DeclarationProbe)
    (canonical : FrontendHandle) : Except String ClassShape := do
  let (occurrence, raw, row) ← source artifact probe canonical
  localFunctionScope probe row.id true
  unless (← canonicalRootEvidence probe occurrence) == canonical do
    throw "class hierarchy: inconsistent canonical identity"
  let _ ← canonicalPredecessorChainEvidence probe occurrence
  let lexical ← lexicalContextChainEvidence artifact probe occurrence
  let semantic ← semanticContextChainEvidence artifact probe occurrence
  unless lexical.map (·.value) == occurrence.lexicalParents.reverse do
    throw "class hierarchy: inconsistent lexical ancestry"
  lexical.forM (fun handle => localFunctionScopeSource artifact probe handle true)
  semantic.forM (fun handle => localFunctionScopeSource artifact probe handle true)
  requireEvidenceText row.raw "record_shape_api" "CXXRecordDecl aggregate member shape v1"
  requireEvidenceText row.raw "record_bases_api" "CXXRecordDecl direct nonvirtual base projection v1"
  unless raw.text "kind" == some "CXXRecordDecl" &&
      (← optionalSourceBool raw "completeDefinition") &&
      (raw.text "tagUsed" == some "class" || raw.text "tagUsed" == some "struct") &&
      raw.text "name" == row.raw.text "name" &&
      (raw.text "name").any cppIdentifier && !(← evidenceBool row.raw "record_union") do
    throw "class hierarchy: unsupported or inconsistent complete class"
  let isAbstract ← evidenceBool row.raw "record_abstract"
  let some data := raw.field "definitionData" | throw "class hierarchy: absent definition data"
  unless isAbstract == (← optionalSourceBool data "isAbstract") do
    throw "class hierarchy: abstractness disagrees with source"
  let attributes := (← children raw).filter (fun child => (child.text "kind").any (·.endsWith "Attr"))
  unless attributes.length == (← evidenceNat row.raw "record_attribute_count") &&
      attributes.all (·.text "kind" == some "VisibilityAttr") do
    throw "class hierarchy: unsupported or inconsistent class attributes"
  let sourceBases ← match raw.field "bases" with
    | none => pure []
    | some (.array values) => pure values
    | _ => throw "class hierarchy: malformed source bases"
  let .array bases ← evidenceField row.raw "record_bases"
    | throw "class hierarchy: malformed base evidence"
  unless bases.length == sourceBases.length &&
      bases.length == (← evidenceNat row.raw "record_base_count") do
    throw "class hierarchy: inconsistent ordered base census"
  let mut parents := []
  for (base, sourceBase) in bases.zip sourceBases do
    if (← evidenceBool base "virtual") || (← optionalSourceBool sourceBase "isVirtual") then
      throw "class hierarchy: virtual base requires shared-subobject semantics"
    let access ← evidenceText base "access"
    let written ← evidenceText base "written_access"
    unless ["public", "protected", "private"].contains access &&
        ["public", "protected", "private", "none"].contains written &&
        sourceBase.text "access" == some access && sourceBase.text "writtenAccess" == some written do
      throw "class hierarchy: inconsistent base access"
    let some sourceType := sourceBase.field "type" | throw "class hierarchy: missing source base type"
    unless sourceType.text "qualType" == some (← evidenceText base "type_spelling") do
      throw "class hierarchy: base source spelling disagrees"
    let .record parent ← parseCppTypeEvidence (← evidenceField base "type")
      | throw "class hierarchy: requires a concrete class base type"
    parents := parents ++ [{target := parent, access, writtenAccess := written}]
  let sourceFields := (← children raw).filter (·.text "kind" == some "FieldDecl")
  unless sourceFields.length == (← evidenceNat row.raw "record_field_count") do
    throw "class hierarchy: inconsistent field census"
  let mut fields := []
  for field in sourceFields do
    let handle ← evidenceHandle field "id"
    let metadata ← localFunctionRow probe handle.value
    unless metadata.kind == "FieldDecl" && metadata.canonical == handle &&
        metadata.semanticContext == some row.id && metadata.lexicalContext == some row.id do
      throw "class hierarchy: inconsistent field ownership"
    fields := fields ++ [handle]
  pure {declaration := canonical, isAbstract, bases := parents, fields}

private def collect : Nat → Artifact → DeclarationProbe → List FrontendHandle →
    List ClassShape → Except String (List ClassShape)
  | _, _, _, [], done => .ok done
  | 0, _, _, _ :: _, _ => .error "class hierarchy: source closure exceeds 128 descriptions"
  | fuel + 1, artifact, probe, next :: pending, done => do
      if done.any (·.declaration == next) then
        collect fuel artifact probe pending done
      else
        let current ← shape artifact probe next
        collect fuel artifact probe (pending ++ current.bases.map (·.target)) (done ++ [current])

def admit (probe : DeclarationProbe) (path : List Nat) : Except String ClassHierarchy := do
  let artifact : Artifact := {
    sourceFile := "", sourceSha256 := "", frontend := .null, dependencies := [], ast := probe.ast}
  let some occurrence := artifact.declarationAtPath path
    | throw "class hierarchy: absent selected declaration"
  unless occurrence.kind == "CXXRecordDecl" do throw "class hierarchy: requires a class declaration"
  let root ← canonicalRootEvidence probe occurrence
  let classes ← collect 128 artifact probe [root] []
  let hierarchy := {root, classes : ClassHierarchy}
  let _ ← hierarchy.slots
  pure hierarchy

end ClassHierarchyAdmission

/-- A complete root and every nonvirtual base occurrence in `hierarchy.slots`
order. Object IDs belong to caller memory; no constructor or layout is guessed. -/
structure ClassReceiverProjection where
  hierarchy : ClassHierarchy
  objects : List ObjectId
  receiverPath : List Nat
  snapshot : IntegralMemberSnapshot
  deriving Repr, BEq, Inhabited

inductive ClassProjectionError where
  | hierarchy (reason : String)
  | malformedWorld
  | absentReceiver
  | wrongReceiver
  | object (reason : ObjectError)
  | getter (reason : MemberGetterError)
  deriving Repr, BEq, Inhabited

namespace ClassReceiverProjection

def check (projection : ClassReceiverProjection) (getter : IntegralMemberGetter) :
    Except ClassProjectionError Unit := do
  let slots ← projection.hierarchy.slots.mapError ClassProjectionError.hierarchy
  let memory := projection.snapshot.memory
  unless projection.objects.length == slots.length &&
      projection.objects.eraseDups.length == projection.objects.length &&
      !projection.objects.contains projection.snapshot.member &&
      memory.values.length == memory.objects.objects.length do throw .malformedWorld
  let some rootId := projection.objects.head? | throw .malformedWorld
  let rootType ← (memory.objects.readType rootId).mapError ClassProjectionError.object
  let constant ← match rootType with
    | .record name =>
        unless name == projection.hierarchy.root do throw .malformedWorld
        pure false
    | .qualified true false (.record name) =>
        unless name == projection.hierarchy.root do throw .malformedWorld
        pure true
    | _ => throw .malformedWorld
  let some root := memory.objects.object? rootId | throw .malformedWorld
  for (slot, objectId) in slots.zip projection.objects do
    let type ← (memory.objects.readType objectId).mapError ClassProjectionError.object
    let some object := memory.objects.object? objectId | throw .malformedWorld
    unless type == integralMemberViewType (.record slot.declaration) constant &&
        object.duration == root.duration && memory.values[objectId]? == some none do
      throw .malformedWorld
  let some (slot, objectId) := (slots.zip projection.objects).find?
      (fun (slot, _) => slot.path == projection.receiverPath) | throw .absentReceiver
  let some shape := projection.hierarchy.classes.find? (·.declaration == slot.declaration)
    | throw .malformedWorld
  unless slot.declaration == getter.owner && objectId == projection.snapshot.object &&
      shape.fields.contains getter.field.declaration do throw .wrongReceiver

def invoke (projection : ClassReceiverProjection) (getter : IntegralMemberGetter) :
    Except ClassProjectionError (IntegralObjectStore × IntegralValue) := do
  projection.check getter
  (getter.invoke projection.snapshot).mapError ClassProjectionError.getter

theorem invoke_of_check (projection : ClassReceiverProjection) (getter : IntegralMemberGetter)
    (memory : IntegralObjectStore) (value : IntegralValue)
    (checked : projection.check getter = .ok ())
    (called : getter.invoke projection.snapshot = .ok (memory, value)) :
    projection.invoke getter = .ok (memory, value) := by
  unfold invoke
  rw [checked]
  change (getter.invoke projection.snapshot).mapError ClassProjectionError.getter = _
  simp [called, Except.mapError]

theorem invoke_memory (projection : ClassReceiverProjection) (getter : IntegralMemberGetter)
    (memory : IntegralObjectStore) (value : IntegralValue)
    (h : projection.invoke getter = .ok (memory, value)) :
    memory = projection.snapshot.memory := by
  unfold invoke at h
  cases hc : projection.check getter with
  | error reason =>
      rw [hc] at h
      change Except.error reason = Except.ok (memory, value) at h
      cases h
  | ok result =>
      cases result
      rw [hc] at h
      change (getter.invoke projection.snapshot).mapError ClassProjectionError.getter = _ at h
      cases hg : getter.invoke projection.snapshot with
      | error reason => simp [hg, Except.mapError] at h
      | ok pair =>
          simp [hg, Except.mapError] at h
          cases h
          exact getter.invoke_memory projection.snapshot memory value hg

end ClassReceiverProjection
end LeanModels.Cpp
