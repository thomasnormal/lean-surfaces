import LeanModels.Cpp.Ast

namespace LeanModels.Cpp

/- A translation artifact may be inspected as a compilation unit before any
   declaration is executable. This is deliberately only a root-shape gate:
   unknown children remain in `Artifact.ast` and are still refused by the
   declaration/body execution boundary below. -/
def admitTranslationUnit (artifact : Artifact) : Except String Unit :=
  match artifact.ast.field "kind" with
  | some (.string "TranslationUnitDecl") => .ok ()
  | some (.string kind) => .error s!"translation: expected TranslationUnitDecl root, got {kind}"
  | some _ => .error "translation: root kind is not a string"
  | none => .error "translation: artifact root has no kind"

/-- Admit one namespace declaration occurrence beneath a valid translation unit.
    The path is an artifact occurrence witness; namespace spelling and child
    execution remain outside this metadata boundary. -/
private def rawAtInnerPath : Raw → List Nat → Option Raw
  | raw, [] => some raw
  | .object fields, index :: rest =>
      match (Raw.object fields).field "inner" with
      | some (.array values) =>
          match values[index]? with
          | some child => rawAtInnerPath child rest
          | none => none
      | _ => none
  | _, _ :: _ => none

def admitNamespaceDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := do
  let _ ← admitTranslationUnit artifact
  unless !path.isEmpty do
    throw "translation: namespace declaration path must be below the translation-unit root"
  let raw := (rawAtInnerPath artifact.ast path).getD .null
  match raw.text "kind" with
  | some "NamespaceDecl" => pure ()
  | some kind => throw s!"translation: expected NamespaceDecl at path, got {kind}"
  | _ => throw "translation: namespace declaration path is absent or malformed"

def executionRefusal : String :=
  "C++ translation-only tier: execution requires object, lifetime, type, expression and statement semantics"

def execute (_artifact : Artifact) (_declarationId : String) : Except String Unit :=
  .error executionRefusal

end LeanModels.Cpp
