import LeanModels.Cpp.Evidence
import LeanModels.Cpp.Types

namespace LeanModels.Cpp

inductive CppTypeEvidence where
  | builtin (type : CppIntType)
  | pointer (pointee : CppTypeEvidence)
  | lvalueReference (referent : CppTypeEvidence)
  | rvalueReference (referent : CppTypeEvidence)
  | qualified (isConst : Bool) (isVolatile : Bool) (base : CppTypeEvidence)
  | function (result : CppTypeEvidence) (parameters : List CppTypeEvidence) (variadic : Bool)
  | record (declaration : FrontendHandle)
  | enumeration (declaration : FrontendHandle)
  deriving Repr, Inhabited

mutual
  /-- Structural equality also reduces for types nested in function parameter lists. -/
  def CppTypeEvidence.beq (left right : CppTypeEvidence) : Bool :=
    match left, right with
    | .builtin left, .builtin right => left == right
    | .pointer left, .pointer right
    | .lvalueReference left, .lvalueReference right
    | .rvalueReference left, .rvalueReference right => left.beq right
    | .qualified lc lv left, .qualified rc rv right =>
        lc == rc && lv == rv && left.beq right
    | .function left lp lv, .function right rp rv =>
        left.beq right && CppTypeEvidence.beqList lp rp && lv == rv
    | .record left, .record right
    | .enumeration left, .enumeration right => left == right
    | _, _ => false
  termination_by structural left

  def CppTypeEvidence.beqList (left right : List CppTypeEvidence) : Bool :=
    match left, right with
    | [], [] => true
    | left :: ls, right :: rs => left.beq right && CppTypeEvidence.beqList ls rs
    | _, _ => false
  termination_by structural left
end

instance : BEq CppTypeEvidence := ⟨CppTypeEvidence.beq⟩

structure TypeEvidenceRow where
  ordinal : Nat
  occurrence : FrontendHandle
  canonical : FrontendHandle
  type : CppTypeEvidence
  deriving Repr, BEq, Inhabited

private def parseBuiltin (name : String) : Except String CppIntType :=
  match name with
  | "bool" => .ok .boolean
  | "char" => .ok .char
  | "signed char" => .ok .signedChar
  | "unsigned char" => .ok .unsignedChar
  | "short" | "short int" => .ok .short
  | "unsigned short" | "unsigned short int" => .ok .unsignedShort
  | "int" => .ok .int
  | "unsigned" | "unsigned int" => .ok .unsignedInt
  | "long" | "long int" => .ok .long
  | "unsigned long" | "unsigned long int" => .ok .unsignedLong
  | "long long" | "long long int" => .ok .longLong
  | "unsigned long long" | "unsigned long long int" => .ok .unsignedLongLong
  | _ => .error s!"unsupported builtin C++ type: {name}"

partial def parseCppTypeEvidence (raw : Raw) : Except String CppTypeEvidence := do
  let kind ← evidenceText raw "kind"
  match kind with
  | "builtin" => .ok (.builtin (← parseBuiltin (← evidenceText raw "name")))
  | "pointer" => .ok (.pointer (← parseCppTypeEvidence (← evidenceField raw "pointee")))
  | "lvalue-reference" =>
      .ok (.lvalueReference (← parseCppTypeEvidence (← evidenceField raw "referent")))
  | "rvalue-reference" =>
      .ok (.rvalueReference (← parseCppTypeEvidence (← evidenceField raw "referent")))
  | "qualified" =>
      let isConst ← evidenceBool raw "const"
      let isVolatile ← evidenceBool raw "volatile"
      if !isConst && !isVolatile then .error "structured type qualifier is empty"
      else .ok (.qualified isConst isVolatile
        (← parseCppTypeEvidence (← evidenceField raw "base")))
  | "function" =>
      let parameters ← match ← evidenceField raw "parameters" with
        | .array values => values.mapM parseCppTypeEvidence
        | _ => .error "structured type parameters: expected array"
      .ok (.function (← parseCppTypeEvidence (← evidenceField raw "result"))
        parameters (← evidenceBool raw "variadic"))
  | "record" => .ok (.record (← evidenceHandle raw "declaration"))
  | "enumeration" => .ok (.enumeration (← evidenceHandle raw "declaration"))
  | _ => .error s!"unsupported structured C++ type kind: {kind}"

private def CppTypeEvidence.referencedHandles : CppTypeEvidence → List FrontendHandle
  | .builtin _ => []
  | .pointer pointee | .lvalueReference pointee | .rvalueReference pointee =>
      pointee.referencedHandles
  | .qualified _ _ base => base.referencedHandles
  | .function result parameters _ =>
      result.referencedHandles ++ parameters.flatMap CppTypeEvidence.referencedHandles
  | .record declaration | .enumeration declaration => [declaration]

private def CppTypeEvidence.containsUnsupportedReference (type : CppTypeEvidence)
    (declarations : List DeclarationEvidenceRow) : Bool :=
  type.referencedHandles.any fun handle =>
    !declarations.any fun declaration => declaration.id == handle

/-- Every record/enum reference in a projected type has declaration metadata. -/
def CppTypeEvidence.referencesKnown (type : CppTypeEvidence)
    (declarations : List DeclarationEvidenceRow) : Bool :=
  !type.containsUnsupportedReference declarations

private def parseTypeEvidenceRow (ordinal : Nat) (raw : Raw) : Except String TypeEvidenceRow := do
  requireEvidenceText raw "type_api" "Clang::QualType structured type projection v1"
  return {
    ordinal
    occurrence := ← evidenceHandle raw "occurrence"
    canonical := ← evidenceHandle raw "canonical"
    type := ← parseCppTypeEvidence (← evidenceField raw "type")
  }

private def sameTypeEvidence (left right : TypeEvidenceRow) : Bool :=
  left.occurrence == right.occurrence && left.canonical == right.canonical &&
    left.type == right.type

def parseTypeEvidenceRows (raw : Raw) : Except String (List TypeEvidenceRow) := do
  let values ← match raw with
    | .array values => .ok values
    | _ => .error "type evidence: expected array"
  values.zipIdx.mapM fun (value, ordinal) => parseTypeEvidenceRow ordinal value

def validateTypeEvidence (probe : DeclarationProbe) (rows : List TypeEvidenceRow) :
    Except String Unit := do
  let rec validate (remaining : List TypeEvidenceRow) (seen : List TypeEvidenceRow) :
      Except String Unit := do
    match remaining with
    | [] => return
    | row :: rest =>
        let occurrences := probe.declarations.filter (fun declaration => declaration.id == row.occurrence)
        if occurrences.isEmpty then
          throw "structured type evidence occurrence is absent from declaration metadata"
        if occurrences.any (fun declaration => declaration.canonical != row.canonical) then
          throw "structured type evidence canonical handle disagrees with declaration metadata"
        if row.type.containsUnsupportedReference probe.declarations then
          throw "structured type evidence references an absent declaration"
        if seen.any (fun prior => prior.occurrence == row.occurrence && !sameTypeEvidence prior row) then
          throw "conflicting structured type evidence for declaration occurrence"
        validate rest (row :: seen)
  validate rows []

def parseValidatedTypeEvidence (probe : DeclarationProbe) :
    Except String (List TypeEvidenceRow) := do
  requireEvidenceText probe.metadata "type_evidence_api"
    "Clang::QualType structured type projection v1"
  let rows ← parseTypeEvidenceRows (← evidenceField probe.metadata "type_evidence")
  validateTypeEvidence probe rows
  return rows

def typeEvidenceFor (rows : List TypeEvidenceRow) (occurrence : FrontendHandle) :
    Option CppTypeEvidence :=
  rows.find? (fun row => row.occurrence == occurrence) |>.map (·.type)

end LeanModels.Cpp
