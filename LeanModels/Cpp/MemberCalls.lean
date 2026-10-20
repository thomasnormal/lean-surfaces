import LeanModels.Cpp.ClassSubobjects

namespace LeanModels.Cpp

/-- A source-backed direct zero-argument call on an existing receiver.
The receiver and method handles are provenance; execution uses the already
validated getter and caller-supplied object projection. -/
structure IntegralMemberCallSyntax where
  method : FrontendHandle
  receiver : FrontendHandle
  receiverType : String
  name : String
  deriving Repr, BEq, Inhabited

inductive IntegralMemberCallSyntaxError where
  | notMemberCall
  | malformedChildren
  | unsupportedReceiver
  | unsupportedArguments
  | missingMethodHandle
  | missingReceiverHandle
  | malformedReceiverType
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

private def callChild (raw : Raw) : Except IntegralMemberCallSyntaxError Raw :=
  match children raw with
  | some [child] => .ok child
  | some (_ :: _ :: _) => .error .unsupportedArguments
  | _ => .error .malformedChildren

def admit (raw : Raw) :
    Except IntegralMemberCallSyntaxError IntegralMemberCallSyntax := do
  unless raw.text "kind" == some "CXXMemberCallExpr" do
    throw .notMemberCall
  let member ← callChild raw
  unless member.text "kind" == some "MemberExpr" do
    throw .malformedChildren
  unless member.field "isArrow" == some (.bool true) &&
      member.text "valueCategory" == some "lvalue" do
    throw .unsupportedReceiver
  let name ← match member.text "name" with
    | some value => pure value
    | none => throw .malformedName
  unless cppIdentifier name do throw .malformedName
  let method ← match member.field "referencedMemberDecl" with
    | some value => (evidenceHandle value "id").mapError (fun _ => .missingMethodHandle)
    | none => throw .missingMethodHandle
  let receiverRaw ← oneChild member
  unless receiverRaw.text "kind" == some "DeclRefExpr" do
    throw .unsupportedReceiver
  let some referenced := receiverRaw.field "referencedDecl"
    | throw .missingReceiverHandle
  let receiver ← (evidenceHandle referenced "id").mapError (fun _ => .missingReceiverHandle)
  let receiverType ← match receiverRaw.field "type" with
    | some type => match type.text "qualType" with
        | some value => if value.isEmpty then throw .malformedReceiverType else pure value
        | none => throw .malformedReceiverType
    | none => throw .malformedReceiverType
  pure {method, receiver, receiverType, name}

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
  | receiverTypeMismatch
  | projection (reason : ClassProjectionError)
  deriving Repr, BEq, Inhabited

namespace IntegralMemberCall

private def projectionReceiverType (projection : ClassReceiverProjection) :
    Except IntegralMemberCallError String := do
  let slots ← projection.hierarchy.slots.mapError
    (fun reason => IntegralMemberCallError.projection (.hierarchy reason))
  let some slot := slots.find? (·.path == projection.receiverPath)
    | throw (.projection .absentReceiver)
  let some shape := projection.hierarchy.classes.find? (·.declaration == slot.declaration)
    | throw (.projection .malformedWorld)
  unless !shape.name.isEmpty do throw .receiverTypeMismatch
  pure (shape.name ++ " *")

/-- Bind source handles to an already admitted getter and receiver projection.
No overload lookup or method selection is performed here. -/
def bind (evidence : IntegralMemberCallSyntax) (getter : IntegralMemberGetter)
    (receiver : FrontendHandle)
    (projection : ClassReceiverProjection) :
    Except IntegralMemberCallError IntegralMemberCall := do
  unless evidence.method == ⟨getter.occurrence.id⟩ do throw .methodMismatch
  unless getter.occurrence.name == some evidence.name do throw .nameMismatch
  unless evidence.receiver == receiver do throw .receiverMismatch
  projection.check getter |>.mapError .projection
  let receiverType ← projectionReceiverType projection
  unless evidence.receiverType == receiverType do throw .receiverTypeMismatch
  pure {getter, projection, syntaxEvidence := evidence}

def invoke (call : IntegralMemberCall) :
    Except IntegralMemberCallError (IntegralObjectStore × IntegralValue) :=
  call.projection.invoke call.getter |>.mapError .projection

end IntegralMemberCall

end LeanModels.Cpp
