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

private def functionTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "f"), ("kind", .string "FunctionDecl"),
        ("name", .string "f"), ("inner", .array [])]])]}

private def variableTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "v"), ("kind", .string "VarDecl"),
        ("name", .string "v"), ("inner", .array [])]])]}

private def enumTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "e"), ("kind", .string "EnumDecl"),
        ("name", .string "Color"), ("inner", .array [])]])]}

private def typedefTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "t"), ("kind", .string "TypedefDecl"),
        ("name", .string "Count"), ("inner", .array [])]])]}

private def typeAliasTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "a"), ("kind", .string "TypeAliasDecl"),
        ("name", .string "Count"), ("inner", .array [])]])]}

private def namespaceAliasTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "n"), ("kind", .string "NamespaceDecl"),
        ("name", .string "n"), ("inner", .array [])],
      .object [("id", .string "a"), ("kind", .string "NamespaceAliasDecl"),
        ("name", .string "alias"), ("inner", .array [])]])]}

private def usingDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "n"), ("kind", .string "NamespaceDecl"),
        ("name", .string "n"), ("inner", .array [])],
      .object [("id", .string "u"), ("kind", .string "UsingDirectiveDecl"),
        ("inner", .array [])]])]}

private def usingTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "n"), ("kind", .string "NamespaceDecl"),
        ("name", .string "n"), ("inner", .array [
          .object [("id", .string "f"), ("kind", .string "FunctionDecl"),
            ("name", .string "f"), ("inner", .array [])]])],
      .object [("id", .string "u"), ("kind", .string "UsingDecl"),
        ("name", .string "f"), ("inner", .array [])]])]}

def namespaceTranslationWitness : Bool :=
  (admitNamespaceDeclaration namespaceTranslation [0]).isOk

def functionTranslationWitness : Except String Unit :=
  admitFunctionDeclaration functionTranslation [0]

def variableTranslationWitness : Except String Unit :=
  admitVariableDeclaration variableTranslation [0]

def enumTranslationWitness : Except String Unit :=
  admitEnumDeclaration enumTranslation [0]

def typedefTranslationWitness : Except String Unit :=
  admitTypedefDeclaration typedefTranslation [0]

def typeAliasTranslationWitness : Except String Unit :=
  admitTypeAliasDeclaration typeAliasTranslation [0]

def namespaceAliasTranslationWitness : Except String Unit :=
  admitNamespaceAliasDeclaration namespaceAliasTranslation [1]

def usingDirectiveTranslationWitness : Except String Unit :=
  admitUsingDirectiveDeclaration usingDirectiveTranslation [1]

def usingTranslationWitness : Except String Unit :=
  admitUsingDeclaration usingTranslation [1]

#guard admitTranslationUnit emptyTranslation matches .ok ()
#guard admitTranslationUnit wrongRoot matches .error _
#guard admitTranslationUnit missingRoot matches .error _
#guard namespaceTranslationWitness
#guard admitNamespaceDeclaration namespaceTranslation [] matches .error _
#guard admitNamespaceDeclaration namespaceTranslation [1] matches .error _
#guard admitNamespaceDeclaration namespaceTranslation [0] matches .ok ()
#guard functionTranslationWitness matches .ok ()
#guard admitFunctionDeclaration functionTranslation [] matches .error _
#guard admitFunctionDeclaration namespaceTranslation [0] matches .error _
#guard variableTranslationWitness matches .ok ()
#guard admitVariableDeclaration variableTranslation [] matches .error _
#guard admitVariableDeclaration functionTranslation [0] matches .error _
#guard enumTranslationWitness matches .ok ()
#guard admitEnumDeclaration enumTranslation [] matches .error _
#guard admitEnumDeclaration functionTranslation [0] matches .error _
#guard typedefTranslationWitness matches .ok ()
#guard admitTypedefDeclaration typedefTranslation [] matches .error _
#guard admitTypedefDeclaration functionTranslation [0] matches .error _
#guard typeAliasTranslationWitness matches .ok ()
#guard admitTypeAliasDeclaration typeAliasTranslation [] matches .error _
#guard admitTypeAliasDeclaration functionTranslation [0] matches .error _
#guard namespaceAliasTranslationWitness matches .ok ()
#guard admitNamespaceAliasDeclaration namespaceAliasTranslation [] matches .error _
#guard admitNamespaceAliasDeclaration namespaceAliasTranslation [0] matches .error _
#guard usingDirectiveTranslationWitness matches .ok ()
#guard admitUsingDirectiveDeclaration usingDirectiveTranslation [] matches .error _
#guard admitUsingDirectiveDeclaration namespaceAliasTranslation [0] matches .error _
#guard usingTranslationWitness matches .ok ()
#guard admitUsingDeclaration usingTranslation [] matches .error _
#guard admitUsingDeclaration usingDirectiveTranslation [1] matches .error _
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
