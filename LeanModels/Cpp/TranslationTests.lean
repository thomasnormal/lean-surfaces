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

private def namespaceTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "ns"), ("kind", .string "NamespaceDecl"),
        ("name", .string "n"), ("inner", .array [])]])]}

def namespaceTranslationWitness : Bool :=
  (admitNamespaceDeclaration namespaceTranslation [0]).isOk

#guard admitTranslationUnit emptyTranslation matches .ok ()
#guard admitTranslationUnit wrongRoot matches .error _
#guard admitTranslationUnit missingRoot matches .error _
#guard namespaceTranslationWitness
#guard admitNamespaceDeclaration namespaceTranslation [] matches .error _
#guard admitNamespaceDeclaration namespaceTranslation [1] matches .error _
#guard admitNamespaceDeclaration namespaceTranslation [0] matches .ok ()
#guard execute emptyTranslation "f" matches .error "C++ translation-only tier: execution requires object, lifetime, type, expression and statement semantics"

theorem empty_translation_admits : admitTranslationUnit emptyTranslation = .ok () := rfl

set_option maxRecDepth 100000 in
theorem wrong_root_refuses : admitTranslationUnit wrongRoot =
    .error "translation: expected TranslationUnitDecl root, got FunctionDecl" := rfl

theorem execution_remains_loud : execute emptyTranslation "f" = .error executionRefusal := rfl

theorem namespace_translation_witness : namespaceTranslationWitness = true := by
  rfl

#print axioms empty_translation_admits
#print axioms wrong_root_refuses
#print axioms execution_remains_loud
#print axioms namespace_translation_witness

end LeanModels.Cpp.TranslationTests
