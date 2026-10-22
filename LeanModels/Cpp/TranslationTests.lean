import LeanModels.Cpp.Translation

namespace LeanModels.Cpp.TranslationTests

private def emptyTranslation : Artifact := {
  sourceFile := "witness.cpp"
  sourceSha256 := "fixture"
  frontend := .null
  dependencies := []
  ast := .object [("kind", .string "TranslationUnitDecl"), ("inner", .array [])]
}

private def wrongRoot : Artifact := {emptyTranslation with
  ast := .object [("kind", .string "FunctionDecl")]
}

private def missingRoot : Artifact := {emptyTranslation with ast := .object []}

#guard admitTranslationUnit emptyTranslation matches .ok ()
#guard admitTranslationUnit wrongRoot matches .error _
#guard admitTranslationUnit missingRoot matches .error _
#guard execute emptyTranslation "f" matches .error "C++ translation-only tier: execution requires object, lifetime, type, expression and statement semantics"

theorem empty_translation_admits : admitTranslationUnit emptyTranslation = .ok () := rfl

set_option maxRecDepth 100000 in
theorem wrong_root_refuses : admitTranslationUnit wrongRoot =
    .error "translation: expected TranslationUnitDecl root, got FunctionDecl" := rfl

theorem execution_remains_loud : execute emptyTranslation "f" = .error executionRefusal := rfl

#print axioms empty_translation_admits
#print axioms wrong_root_refuses
#print axioms execution_remains_loud

end LeanModels.Cpp.TranslationTests
