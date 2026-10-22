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

private def parameterTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "f"), ("kind", .string "FunctionDecl"),
        ("name", .string "f"), ("inner", .array [
          .object [("id", .string "p"), ("kind", .string "ParmVarDecl"),
            ("name", .string "x"), ("inner", .array [])]])]])]}

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
        ("name", .string "Color"), ("inner", .array [
          .object [("id", .string "red"), ("kind", .string "EnumConstantDecl"),
            ("name", .string "red"), ("inner", .array [])]])]])]}

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

private def linkageTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "l"), ("kind", .string "LinkageSpecDecl"),
        ("language", .string "C"), ("inner", .array [])]])]}

private def staticAssertTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "s"), ("kind", .string "StaticAssertDecl"),
        ("inner", .array [])]])]}

private def recordTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "r"), ("kind", .string "CXXRecordDecl"),
        ("name", .string "Sample"), ("tagUsed", .string "struct"),
        ("inner", .array [
          .object [("id", .string "m"), ("kind", .string "FieldDecl"),
            ("name", .string "value"), ("inner", .array [])],
          .object [("id", .string "f"), ("kind", .string "CXXMethodDecl"),
            ("name", .string "get"), ("inner", .array [])],
          .object [("id", .string "a"), ("kind", .string "AccessSpecDecl"),
            ("access", .string "public"), ("inner", .array [])],
          .object [("id", .string "c"), ("kind", .string "CXXConstructorDecl"),
            ("name", .string "Sample"), ("inner", .array [])],
          .object [("id", .string "d"), ("kind", .string "CXXDestructorDecl"),
            ("name", .string "~Sample"), ("inner", .array [])],
          .object [("id", .string "v"), ("kind", .string "CXXConversionDecl"),
            ("name", .string "operator int"), ("inner", .array [])],
          .object [("id", .string "y"), ("kind", .string "FriendDecl"),
            ("inner", .array [])]])]])]}

private def templateParameterTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "t"), ("kind", .string "ClassTemplateDecl"),
        ("name", .string "Sample"), ("inner", .array [
          .object [("id", .string "p"), ("kind", .string "TemplateTypeParmDecl"),
            ("name", .string "T"), ("inner", .array [])]])]])]}

def namespaceTranslationWitness : Bool :=
  (admitNamespaceDeclaration namespaceTranslation [0]).isOk

def functionTranslationWitness : Except String Unit :=
  admitFunctionDeclaration functionTranslation [0]

def parameterTranslationWitness : Except String Unit :=
  admitParameterDeclaration parameterTranslation [0, 0]

def recordTranslationWitness : Except String Unit :=
  admitRecordDeclaration recordTranslation [0]

def fieldTranslationWitness : Except String Unit :=
  admitFieldDeclaration recordTranslation [0, 0]

def methodTranslationWitness : Except String Unit :=
  admitMethodDeclaration recordTranslation [0, 1]

def accessTranslationWitness : Except String Unit :=
  admitAccessSpecification recordTranslation [0, 2]

def constructorTranslationWitness : Except String Unit :=
  admitConstructorDeclaration recordTranslation [0, 3]

def destructorTranslationWitness : Except String Unit :=
  admitDestructorDeclaration recordTranslation [0, 4]

def conversionTranslationWitness : Except String Unit :=
  admitConversionDeclaration recordTranslation [0, 5]

def friendTranslationWitness : Except String Unit :=
  admitFriendDeclaration recordTranslation [0, 6]

def templateParameterTranslationWitness : Except String Unit :=
  admitTemplateTypeParameter templateParameterTranslation [0, 0]

def variableTranslationWitness : Except String Unit :=
  admitVariableDeclaration variableTranslation [0]

def enumTranslationWitness : Except String Unit :=
  admitEnumDeclaration enumTranslation [0]

def enumConstantTranslationWitness : Except String Unit :=
  admitEnumConstantDeclaration enumTranslation [0, 0]

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

def linkageTranslationWitness : Except String Unit :=
  admitLinkageSpecification linkageTranslation [0]

def staticAssertTranslationWitness : Except String Unit :=
  admitStaticAssertion staticAssertTranslation [0]

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
#guard parameterTranslationWitness matches .ok ()
#guard admitParameterDeclaration parameterTranslation [] matches .error _
#guard admitParameterDeclaration functionTranslation [0] matches .error _
#guard recordTranslationWitness matches .ok ()
#guard admitRecordDeclaration recordTranslation [] matches .error _
#guard admitRecordDeclaration functionTranslation [0] matches .error _
#guard fieldTranslationWitness matches .ok ()
#guard admitFieldDeclaration recordTranslation [] matches .error _
#guard admitFieldDeclaration functionTranslation [0] matches .error _
#guard methodTranslationWitness matches .ok ()
#guard admitMethodDeclaration recordTranslation [] matches .error _
#guard admitMethodDeclaration functionTranslation [0] matches .error _
#guard accessTranslationWitness matches .ok ()
#guard admitAccessSpecification recordTranslation [] matches .error _
#guard admitAccessSpecification functionTranslation [0] matches .error _
#guard constructorTranslationWitness matches .ok ()
#guard admitConstructorDeclaration recordTranslation [] matches .error _
#guard admitConstructorDeclaration functionTranslation [0] matches .error _
#guard destructorTranslationWitness matches .ok ()
#guard admitDestructorDeclaration recordTranslation [] matches .error _
#guard admitDestructorDeclaration functionTranslation [0] matches .error _
#guard conversionTranslationWitness matches .ok ()
#guard admitConversionDeclaration recordTranslation [] matches .error _
#guard admitConversionDeclaration functionTranslation [0] matches .error _
#guard friendTranslationWitness matches .ok ()
#guard admitFriendDeclaration recordTranslation [] matches .error _
#guard admitFriendDeclaration functionTranslation [0] matches .error _
#guard templateParameterTranslationWitness matches .ok ()
#guard admitTemplateTypeParameter templateParameterTranslation [] matches .error _
#guard admitTemplateTypeParameter functionTranslation [0] matches .error _
#guard variableTranslationWitness matches .ok ()
#guard admitVariableDeclaration variableTranslation [] matches .error _
#guard admitVariableDeclaration functionTranslation [0] matches .error _
#guard enumTranslationWitness matches .ok ()
#guard admitEnumDeclaration enumTranslation [] matches .error _
#guard admitEnumDeclaration functionTranslation [0] matches .error _
#guard enumConstantTranslationWitness matches .ok ()
#guard admitEnumConstantDeclaration enumTranslation [] matches .error _
#guard admitEnumConstantDeclaration functionTranslation [0] matches .error _
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
#guard linkageTranslationWitness matches .ok ()
#guard admitLinkageSpecification linkageTranslation [] matches .error _
#guard admitLinkageSpecification usingTranslation [1] matches .error _
#guard staticAssertTranslationWitness matches .ok ()
#guard admitStaticAssertion staticAssertTranslation [] matches .error _
#guard admitStaticAssertion usingTranslation [1] matches .error _
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
