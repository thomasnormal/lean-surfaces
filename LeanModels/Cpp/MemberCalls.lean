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
  deriving Repr, BEq, Inhabited

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
  let (receiverRaw, receiverCasts) ← receiverDeclRef receiverRawOuter
  let some referenced := receiverRaw.field "referencedDecl"
    | throw .missingReceiverHandle
  let receiver ← (evidenceHandle referenced "id").mapError (fun _ => .missingReceiverHandle)
  let receiverType ← match receiverRawOuter.field "type" with
    | some type => match type.text "qualType" with
        | some value => if value.isEmpty then throw .malformedReceiverType else pure value
        | none => throw .malformedReceiverType
    | none => throw .malformedReceiverType
  let resultType ← resultSpelling raw
  let receiverCast := receiverCasts
  pure {(default : IntegralMemberCallSyntax) with
    method := method, receiver := receiver, receiverType := receiverType,
    resultType := resultType, name := name, canonicalMethod := method,
    receiverIsArrow := receiverIsArrow, receiverCast := receiverCast}

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
