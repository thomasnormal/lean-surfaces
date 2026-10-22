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

private def admitDeclarationKind (artifact : Artifact) (path : List Nat)
    (expected : String) (label : String) : Except String Unit := do
  let _ ← admitTranslationUnit artifact
  unless !path.isEmpty do
    throw s!"translation: {label} declaration path must be below the translation-unit root"
  let raw := (rawAtInnerPath artifact.ast path).getD .null
  match raw.text "kind" with
  | some kind =>
      if kind == expected then pure ()
      else throw s!"translation: expected {expected} at path, got {kind}"
  | _ => throw s!"translation: {label} declaration path is absent or malformed"

def admitNamespaceDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "NamespaceDecl" "namespace"

def admitFunctionDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "FunctionDecl" "function"

def admitParameterDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ParmVarDecl" "parameter"

def admitVariableDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "VarDecl" "variable"

def admitEnumDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "EnumDecl" "enum"

def admitTypedefDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "TypedefDecl" "typedef"

def admitTypeAliasDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "TypeAliasDecl" "type-alias"

def admitNamespaceAliasDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "NamespaceAliasDecl" "namespace-alias"

def admitUsingDirectiveDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "UsingDirectiveDecl" "using-directive"

def admitUsingDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "UsingDecl" "using"

def admitLinkageSpecification (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "LinkageSpecDecl" "linkage-specification"

def admitStaticAssertion (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "StaticAssertDecl" "static-assertion"

def executionRefusal : String :=
  "C++ translation-only tier: execution requires object, lifetime, type, expression and statement semantics"

def execute (_artifact : Artifact) (_declarationId : String) : Except String Unit :=
  .error executionRefusal

end LeanModels.Cpp
