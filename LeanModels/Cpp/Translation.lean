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

def executionRefusal : String :=
  "C++ translation-only tier: execution requires object, lifetime, type, expression and statement semantics"

def execute (_artifact : Artifact) (_declarationId : String) : Except String Unit :=
  .error executionRefusal

end LeanModels.Cpp
