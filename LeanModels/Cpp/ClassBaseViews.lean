import LeanModels.Cpp.ClassSubobjects

namespace LeanModels.Cpp

/-- An existing-object nonvirtual base view. Paths identify occurrences in the
closed hierarchy; no ABI offset, allocation, dynamic cast or source access
check is inferred here. An optional declaring-class context permits the narrow
protected/private policy below. -/
structure ClassBaseView where
  hierarchy : ClassHierarchy
  objects : List ObjectId
  sourcePath : List Nat
  targetPath : List Nat
  memory : IntegralObjectStore
  /-- Optional declaring-class context for protected/private access. -/
  accessContext : Option FrontendHandle := none
  deriving Repr, BEq, Inhabited

inductive ClassBaseViewError where
  | hierarchy (reason : String)
  | malformedWorld
  | missingSource
  | missingTarget
  | nonBasePath
  | sameSubobject
  | inaccessibleBase
  deriving Repr, BEq, Inhabited

structure ClassBaseCastSyntax where
  sourceType : String
  targetType : String
  operand : FrontendHandle
  basePath : List String
  deriving Repr, BEq, Inhabited

/- An explicit typed nonvirtual base cast. The source and target declarations
are witnesses for an already selected path; no source expression is parsed. -/
structure ClassBaseCast where
  view : ClassBaseView
  sourceDeclaration : FrontendHandle
  targetDeclaration : FrontendHandle
  /-- Optional source AST evidence attached by `ClassBaseCastSyntax.bind`. -/
  syntaxEvidence : Option ClassBaseCastSyntax := none
  deriving Repr, BEq, Inhabited

inductive ClassBaseCastError where
  | view (reason : ClassBaseViewError)
  | sourceTypeMismatch
  | targetTypeMismatch
  deriving Repr, BEq, Inhabited

inductive ClassBaseCastSyntaxError where
  | notStaticCast
  | unsupportedCastKind
  | malformedType
  | malformedChildren
  | missingBasePath
  | unsupportedOperand
  deriving Repr, BEq, Inhabited

namespace ClassBaseCastSyntax

private def typeSpelling (raw : Raw) : Option String := do
  let type ← raw.field "type"
  type.text "qualType"

private def oneChild (raw : Raw) : Option Raw := do
  let some (.array [child]) := raw.field "inner" | none
  pure child

private def pathNames (raw : Raw) : Except ClassBaseCastSyntaxError (List String) :=
  match raw.field "path" with
  | some (.array values) =>
      match values with
      | [] => .error .missingBasePath
      | _ => values.mapM fun edge =>
          match edge.text "name" with
          | some name => .ok name
          | none => .error .malformedChildren
  | _ => .error .missingBasePath

private def pointerType (spelling : String) : Bool :=
  match spelling.toList.reverse with
  | '*' :: ' ' :: _ => true
  | _ => false

def admit (raw : Raw) (sourceType targetType : String) :
    Except ClassBaseCastSyntaxError ClassBaseCastSyntax := do
  unless raw.text "kind" == some "CXXStaticCastExpr" do
    throw .notStaticCast
  unless raw.text "castKind" == some "NoOp" do
    throw .unsupportedCastKind
  unless pointerType sourceType && pointerType targetType &&
      sourceType != targetType do
    throw .malformedType
  unless typeSpelling raw == some targetType do
    throw .malformedType
  let some child := oneChild raw | throw .malformedChildren
  unless child.text "kind" == some "ImplicitCastExpr" &&
      child.text "castKind" == some "DerivedToBase" &&
      typeSpelling child == some targetType do
    throw .unsupportedCastKind
  let basePath ← pathNames child
  let some lvalue := oneChild child | throw .malformedChildren
  unless lvalue.text "kind" == some "ImplicitCastExpr" &&
      lvalue.text "castKind" == some "LValueToRValue" &&
      typeSpelling lvalue == some sourceType do
    throw .malformedChildren
  let some operand := oneChild lvalue | throw .malformedChildren
  unless operand.text "kind" == some "DeclRefExpr" &&
      typeSpelling operand == some sourceType do
    throw .unsupportedOperand
  let some referenced := operand.field "referencedDecl" | throw .unsupportedOperand
  let operandHandle ← (evidenceHandle referenced "id").mapError (fun _ => .unsupportedOperand)
  pure {sourceType, targetType, operand := operandHandle, basePath}

/-- Attach an admitted source-level shape to the already-resolved typed cast.
The typed cast carries declaration handles and paths; the syntax record carries
the corresponding frontend spellings, so no runtime field needs to be copied. -/
def bind (_admitted : ClassBaseCastSyntax) (cast : ClassBaseCast) : ClassBaseCast :=
  {cast with syntaxEvidence := some _admitted}

end ClassBaseCastSyntax

namespace ClassBaseView

private def isPrefix : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | first :: rest, other :: tail => first == other && isPrefix rest tail

def slotAt (slots : List ClassSubobjectSlot) (path : List Nat) :
    Option (ClassSubobjectSlot × ObjectId) :=
  (slots.zipIdx.find? (fun (slot, _) => slot.path == path)).map
    (fun (slot, index) => (slot, index))

private def hierarchySlots (hierarchy : ClassHierarchy) :
    Except ClassBaseViewError (List ClassSubobjectSlot) :=
  match hierarchy.slots with
  | .ok slots => .ok slots
  | .error reason => .error (.hierarchy reason)

private def suffixOf : List Nat → List Nat → Option (List Nat)
  | [], target => some target
  | _ :: _, [] => none
  | first :: rest, other :: tail =>
      if first == other then suffixOf rest tail else none

private def derivesFrom : Nat → ClassHierarchy → FrontendHandle → FrontendHandle → Bool
  | 0, _, _, _ => false
  | fuel + 1, hierarchy, descendant, ancestor =>
      descendant == ancestor ||
        match hierarchy.classes.find? (·.declaration == descendant) with
        | none => false
        | some shape => shape.bases.any (fun edge =>
            derivesFrom fuel hierarchy edge.target ancestor)

private def accessAllowed (hierarchy : ClassHierarchy)
    (context : Option FrontendHandle) (owner : FrontendHandle) (edge : ClassBaseSpec) : Bool :=
  edge.access == "public" || match context with
    | none => false
    | some current =>
        if current == owner then true
        else
          match hierarchy.classes.find? (·.declaration == owner) with
          | some shape =>
              shape.friends.contains current ||
                (edge.access == "protected" &&
                  derivesFrom (hierarchy.classes.length + 1) hierarchy current owner)
          | none => false

private def accessibleEdges (hierarchy : ClassHierarchy)
    (context : Option FrontendHandle) (slots : List ClassSubobjectSlot) :
    List Nat → List Nat → Bool
  | _, [] => true
  | path, index :: rest =>
      match slotAt slots path with
      | none => false
      | some (slot, _) =>
          match hierarchy.classes.find? (·.declaration == slot.declaration) with
          | none => false
          | some shape =>
              match shape.bases[index]? with
              | none => false
              | some edge =>
                  accessAllowed hierarchy context slot.declaration edge &&
                    accessibleEdges hierarchy context slots (path ++ [index]) rest

/-- Validate the complete root and every supplied nonvirtual occurrence before
    allowing a source-prefix view to select its target identity. -/
def check (view : ClassBaseView) : Except ClassBaseViewError Unit := do
  let slots ← hierarchySlots view.hierarchy
  unless view.objects.length == slots.length &&
      view.objects.eraseDups.length == view.objects.length &&
      view.memory.values.length == view.memory.objects.objects.length do
    throw .malformedWorld
  let some rootId := view.objects.head? | throw .malformedWorld
  let rootType ← (view.memory.objects.readType rootId).mapError (fun _ => .malformedWorld)
  let constant ← match rootType with
    | .record name =>
        unless name == view.hierarchy.root do throw .malformedWorld
        pure false
    | .qualified true false (.record name) =>
        unless name == view.hierarchy.root do throw .malformedWorld
        pure true
    | _ => throw .malformedWorld
  let some root := view.memory.objects.object? rootId | throw .malformedWorld
  for (slot, objectId) in slots.zip view.objects do
    let type ← (view.memory.objects.readType objectId).mapError (fun _ => .malformedWorld)
    let some object := view.memory.objects.object? objectId | throw .malformedWorld
    unless type == integralMemberViewType (.record slot.declaration) constant &&
        object.duration == root.duration && object.phase == .aliveInitialized &&
        view.memory.values[objectId]? == some none do
      throw .malformedWorld
  let some (source, sourceId) := slotAt slots view.sourcePath | throw .missingSource
  let some (target, targetId) := slotAt slots view.targetPath | throw .missingTarget
  unless source.path != target.path && isPrefix source.path target.path do
    throw .nonBasePath
  let some edges := suffixOf source.path target.path | throw .nonBasePath
  unless accessibleEdges view.hierarchy view.accessContext slots source.path edges do
    throw .inaccessibleBase
  unless sourceId != targetId && source.declaration != target.declaration do
    throw .sameSubobject

def convert (view : ClassBaseView) :
    Except ClassBaseViewError (IntegralObjectStore × ObjectId) := do
  match view.check with
  | .error reason => .error reason
  | .ok _ =>
      match hierarchySlots view.hierarchy with
      | .error reason => .error reason
      | .ok slots =>
          match slotAt slots view.targetPath with
          | none => .error .missingTarget
          | some (_, targetId) => .ok (view.memory, targetId)

theorem convert_of_check (view : ClassBaseView) (memory : IntegralObjectStore)
    (object : ObjectId) (checked : view.check = .ok ())
    (target : view.convert = .ok (memory, object)) :
    memory = view.memory := by
  unfold convert at target
  rw [checked] at target
  cases hs : hierarchySlots view.hierarchy with
  | error reason => simp [hs] at target
  | ok slots =>
      cases ht : slotAt slots view.targetPath with
      | none => simp [hs, ht] at target
      | some pair =>
          simp [hs, ht] at target
          exact target.1.symm

theorem convert_memory (view : ClassBaseView) (memory : IntegralObjectStore)
    (object : ObjectId) (h : view.convert = .ok (memory, object)) :
    memory = view.memory := by
  unfold convert at h
  cases hc : view.check with
  | error reason => simp [hc] at h
  | ok result =>
      cases hs : hierarchySlots view.hierarchy with
      | error reason => simp [hc, hs] at h
      | ok slots =>
          cases ht : slotAt slots view.targetPath with
          | none => simp [hc, hs, ht] at h
          | some pair =>
              simp [hc, hs, ht] at h
              exact h.1.symm

end ClassBaseView

namespace ClassBaseCast

private def slots (cast : ClassBaseCast) :
    Except ClassBaseCastError (List ClassSubobjectSlot) :=
  match cast.view.hierarchy.slots with
  | .ok slots => .ok slots
  | .error reason => .error (.view (.hierarchy reason))

def check (cast : ClassBaseCast) : Except ClassBaseCastError Unit := do
  cast.view.check.mapError ClassBaseCastError.view
  let slots ← cast.slots
  let some source := ClassBaseView.slotAt slots cast.view.sourcePath
    | throw (.view .missingSource)
  let some target := ClassBaseView.slotAt slots cast.view.targetPath
    | throw (.view .missingTarget)
  unless source.1.declaration == cast.sourceDeclaration do
    throw .sourceTypeMismatch
  unless target.1.declaration == cast.targetDeclaration do
    throw .targetTypeMismatch

def execute (cast : ClassBaseCast) :
    Except ClassBaseCastError (IntegralObjectStore × ObjectId) :=
  match cast.check with
  | .error reason => .error reason
  | .ok _ => cast.view.convert.mapError ClassBaseCastError.view

theorem execute_memory (cast : ClassBaseCast)
    (memory : IntegralObjectStore) (object : ObjectId)
    (h : cast.execute = .ok (memory, object)) :
    memory = cast.view.memory := by
  unfold execute at h
  cases hc : cast.check with
  | error reason => simp [hc] at h
  | ok result =>
      cases hv : cast.view.convert with
      | error reason => simp [hc, hv, Except.mapError] at h
      | ok pair =>
          simp [hc, hv] at h
          cases h
          exact cast.view.convert_memory _ _ hv

end ClassBaseCast
end LeanModels.Cpp
