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

private def baseSpecifierTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "b"), ("kind", .string "CXXBaseSpecifier"),
        ("name", .string "Base"), ("inner", .array [])]])]}

private def templateParameterTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "t"), ("kind", .string "ClassTemplateDecl"),
        ("name", .string "Sample"), ("inner", .array [
          .object [("id", .string "p"), ("kind", .string "TemplateTypeParmDecl"),
            ("name", .string "T"), ("inner", .array [])],
          .object [("id", .string "n"), ("kind", .string "NonTypeTemplateParmDecl"),
            ("name", .string "N"), ("inner", .array [])],
          .object [("id", .string "q"), ("kind", .string "TemplateTemplateParmDecl"),
            ("name", .string "Q"), ("inner", .array [])]])]])]}

private def functionTemplateTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "f"), ("kind", .string "FunctionTemplateDecl"),
        ("name", .string "identity"), ("inner", .array [])]])]}

private def variableTemplateTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "v"), ("kind", .string "VarTemplateDecl"),
        ("name", .string "value"), ("inner", .array [])]])]}

private def typeAliasTemplateTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "a"), ("kind", .string "TypeAliasTemplateDecl"),
        ("name", .string "Alias"), ("inner", .array [])]])]}

private def classTemplateSpecializationTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "s"), ("kind", .string "ClassTemplateSpecializationDecl"),
        ("name", .string "Sample"), ("inner", .array [])]])]}

private def variableTemplateSpecializationTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "s"), ("kind", .string "VarTemplateSpecializationDecl"),
        ("name", .string "value"), ("inner", .array [])]])]}

private def classTemplatePartialSpecializationTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "p"), ("kind", .string "ClassTemplatePartialSpecializationDecl"),
        ("name", .string "Sample"), ("inner", .array [])]])]}

private def variableTemplatePartialSpecializationTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "p"), ("kind", .string "VarTemplatePartialSpecializationDecl"),
        ("name", .string "value"), ("inner", .array [])]])]}

private def conceptTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "c"), ("kind", .string "ConceptDecl"),
        ("name", .string "Integral"), ("inner", .array [])]])]}

private def deductionGuideTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "g"), ("kind", .string "CXXDeductionGuideDecl"),
        ("name", .string "Box"), ("inner", .array [])]])]}

private def usingShadowTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "s"), ("kind", .string "UsingShadowDecl"),
        ("name", .string "value"), ("inner", .array [])]])]}

private def constructorUsingShadowTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "s"), ("kind", .string "ConstructorUsingShadowDecl"),
        ("name", .string "Base"), ("inner", .array [])]])]}

private def usingPackTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "p"), ("kind", .string "UsingPackDecl"),
        ("name", .string "operator()"), ("inner", .array [])]])]}

private def unresolvedUsingTypenameTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "u"), ("kind", .string "UnresolvedUsingTypenameDecl"),
        ("name", .string "type"), ("inner", .array [])]])]}

private def unresolvedUsingValueTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "u"), ("kind", .string "UnresolvedUsingValueDecl"),
        ("name", .string "value"), ("inner", .array [])]])]}

private def bindingTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "b"), ("kind", .string "BindingDecl"),
        ("name", .string "first"), ("inner", .array [])]])]}

private def decompositionTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "d"), ("kind", .string "DecompositionDecl"),
        ("name", .string "pair"), ("inner", .array [])]])]}

private def indirectFieldTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "i"), ("kind", .string "IndirectFieldDecl"),
        ("name", .string "first"), ("inner", .array [])]])]}

private def classScopeFunctionSpecializationTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "s"), ("kind", .string "ClassScopeFunctionSpecializationDecl"),
        ("name", .string "f"), ("inner", .array [])]])]}

private def friendTemplateTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "f"), ("kind", .string "FriendTemplateDecl"),
        ("name", .string "friend"), ("inner", .array [])]])]}

private def templateParamObjectTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "TemplateParamObjectDecl"),
        ("name", .string "value"), ("inner", .array [])]])]}

private def implicitConceptSpecializationTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "i"), ("kind", .string "ImplicitConceptSpecializationDecl"),
        ("name", .string "C"), ("inner", .array [])]])]}

private def requiresExpressionTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "r"), ("kind", .string "RequiresExpr"),
        ("name", .string "requires"), ("inner", .array [])]])]}

private def typeRequirementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "t"), ("kind", .string "TypeRequirement"),
        ("name", .string "type"), ("inner", .array [])]])]}

private def simpleRequirementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "s"), ("kind", .string "SimpleRequirement"),
        ("name", .string "simple"), ("inner", .array [])]])]}

private def compoundRequirementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "c"), ("kind", .string "CompoundRequirement"),
        ("name", .string "compound"), ("inner", .array [])]])]}

private def nestedRequirementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "n"), ("kind", .string "NestedRequirement"),
        ("name", .string "nested"), ("inner", .array [])]])]}

private def usingEnumTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "u"), ("kind", .string "UsingEnumDecl"),
        ("name", .string "Color"), ("inner", .array [])]])]}

private def lifetimeExtendedTemporaryTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "l"), ("kind", .string "LifetimeExtendedTemporaryDecl"),
        ("name", .string "temporary"), ("inner", .array [])]])]}

private def materializeTemporaryTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "m"), ("kind", .string "MaterializeTemporaryExpr"),
        ("name", .string "materialize"), ("inner", .array [])]])]}

private def bindTemporaryTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "b"), ("kind", .string "CXXBindTemporaryExpr"),
        ("name", .string "bind"), ("inner", .array [])]])]}

private def expressionWithCleanupsTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "e"), ("kind", .string "ExprWithCleanups"),
        ("name", .string "cleanup"), ("inner", .array [])]])]}

private def temporaryObjectTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "CXXTemporaryObjectExpr"),
        ("name", .string "temporary"), ("inner", .array [])]])]}

private def cxxConstructExpressionTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "c"), ("kind", .string "CXXConstructExpr"),
        ("name", .string "construct"), ("inner", .array [])]])]}

private def newTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "n"), ("kind", .string "CXXNewExpr"),
        ("name", .string "new"), ("inner", .array [])]])]}

private def deleteTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "d"), ("kind", .string "CXXDeleteExpr"),
        ("name", .string "delete"), ("inner", .array [])]])]}

private def defaultInitTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "i"), ("kind", .string "CXXDefaultInitExpr"),
        ("name", .string "default"), ("inner", .array [])]])]}

private def scalarValueInitTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "s"), ("kind", .string "CXXScalarValueInitExpr"),
        ("name", .string "zero"), ("inner", .array [])]])]}

private def initializerListTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "l"), ("kind", .string "InitListExpr"),
        ("name", .string "list"), ("inner", .array [])]])]}

private def parenListInitTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "p"), ("kind", .string "CXXParenListInitExpr"),
        ("name", .string "paren-list"), ("inner", .array [])]])]}

private def implicitValueInitTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "v"), ("kind", .string "ImplicitValueInitExpr"),
        ("name", .string "zero"), ("inner", .array [])]])]}

private def implicitCastTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "c"), ("kind", .string "ImplicitCastExpr"),
        ("castKind", .string "IntegralCast"), ("name", .string "cast"),
        ("inner", .array [])]])]}

private def parenthesizedTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "p"), ("kind", .string "ParenExpr"),
        ("name", .string "paren"), ("inner", .array [])]])]}

private def constantTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "k"), ("kind", .string "ConstantExpr"),
        ("name", .string "constant"), ("inner", .array [])]])]}

private def staticCastTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "s"), ("kind", .string "CXXStaticCastExpr"),
        ("castKind", .string "IntegralCast"), ("name", .string "cast"),
        ("inner", .array [])]])]}

private def constCastTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "c"), ("kind", .string "CXXConstCastExpr"),
        ("castKind", .string "NoOp"), ("name", .string "cast"),
        ("inner", .array [])]])]}

private def reinterpretCastTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "r"), ("kind", .string "CXXReinterpretCastExpr"),
        ("castKind", .string "IntegralToPointer"), ("name", .string "cast"),
        ("inner", .array [])]])]}

private def dynamicCastTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "d"), ("kind", .string "CXXDynamicCastExpr"),
        ("castKind", .string "Dynamic"), ("name", .string "cast"),
        ("inner", .array [])]])]}

private def boolLiteralTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "b"), ("kind", .string "CXXBoolLiteralExpr"),
        ("value", .bool true), ("name", .string "literal"),
        ("inner", .array [])]])]}

private def nullPtrLiteralTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "n"), ("kind", .string "CXXNullPtrLiteralExpr"),
        ("name", .string "nullptr"), ("inner", .array [])]])]}

private def characterLiteralTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "c"), ("kind", .string "CharacterLiteral"),
        ("value", .number "97"), ("name", .string "literal"),
        ("inner", .array [])]])]}

private def floatingLiteralTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "f"), ("kind", .string "FloatingLiteral"),
        ("value", .string "1.5"), ("name", .string "literal"),
        ("inner", .array [])]])]}

private def stringLiteralTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "s"), ("kind", .string "StringLiteral"),
        ("value", .string "hello"), ("name", .string "literal"),
        ("inner", .array [])]])]}

private def integerLiteralTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "i"), ("kind", .string "IntegerLiteral"),
        ("value", .number "42"), ("name", .string "literal"),
        ("inner", .array [])]])]}

private def declarationReferenceTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "r"), ("kind", .string "DeclRefExpr"),
        ("name", .string "value"), ("referencedDecl", .object [
          ("id", .string "v"), ("kind", .string "VarDecl")]),
        ("inner", .array [])]])]}

private def thisTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "t"), ("kind", .string "CXXThisExpr"),
        ("type", .object [("qualType", .string "S *")]),
        ("name", .string "this"), ("inner", .array [])]])]}

private def unaryOperatorTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "u"), ("kind", .string "UnaryOperator"),
        ("opcode", .string "-"), ("name", .string "negate"),
        ("inner", .array [])]])]}

private def binaryOperatorTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "b"), ("kind", .string "BinaryOperator"),
        ("opcode", .string "+"), ("name", .string "add"),
        ("inner", .array [])]])]}

private def cxxRewrittenBinaryOperatorTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "r"), ("kind", .string "CXXRewrittenBinaryOperator"),
        ("opcode", .string "=="), ("name", .string "rewritten-equality"),
        ("inner", .array [])]])]}

private def cxxNoexceptTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "n"), ("kind", .string "CXXNoexceptExpr"),
        ("name", .string "noexcept"), ("inner", .array [])]])]}

private def cxxTypeidTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "t"), ("kind", .string "CXXTypeidExpr"),
        ("name", .string "typeid"), ("inner", .array [])]])]}

private def cxxFoldTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "f"), ("kind", .string "CXXFoldExpr"),
        ("name", .string "fold"), ("inner", .array [])]])]}

private def cxxCoawaitTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "a"), ("kind", .string "CXXCoawaitExpr"),
        ("name", .string "co_await"), ("inner", .array [])]])]}

private def cStyleCastTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "c"), ("kind", .string "CStyleCastExpr"),
        ("name", .string "cast"), ("inner", .array [])]])]}

private def unaryExprOrTypeTraitTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "s"), ("kind", .string "UnaryExprOrTypeTraitExpr"),
        ("name", .string "sizeof"), ("inner", .array [])]])]}

private def vaArgTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "v"), ("kind", .string "VAArgExpr"),
        ("name", .string "va_arg"), ("inner", .array [])]])]}

private def cxxDependentScopeMemberTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "m"), ("kind", .string "CXXDependentScopeMemberExpr"),
        ("name", .string "member"), ("inner", .array [])]])]}

private def cxxDefaultArgumentTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "a"), ("kind", .string "CXXDefaultArgExpr"),
        ("name", .string "default"), ("inner", .array [])]])]}

private def cxxUnresolvedConstructTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "u"), ("kind", .string "CXXUnresolvedConstructExpr"),
        ("name", .string "construct"), ("inner", .array [])]])]}

private def unresolvedLookupTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "l"), ("kind", .string "UnresolvedLookupExpr"),
        ("name", .string "lookup"), ("inner", .array [])]])]}

private def cxxPseudoDestructorTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "p"), ("kind", .string "CXXPseudoDestructorExpr"),
        ("name", .string "destroy"), ("inner", .array [])]])]}

private def cxxUnresolvedMemberTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "m"), ("kind", .string "CXXUnresolvedMemberExpr"),
        ("name", .string "member"), ("inner", .array [])]])]}

private def cxxDependentScopeDeclRefTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "d"), ("kind", .string "CXXDependentScopeDeclRefExpr"),
        ("name", .string "reference"), ("inner", .array [])]])]}

private def cxxInheritedConstructorInitTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "i"), ("kind", .string "CXXInheritedCtorInitExpr"),
        ("name", .string "initializer"), ("inner", .array [])]])]}

private def cxxStdInitializerListTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "s"), ("kind", .string "CXXStdInitializerListExpr"),
        ("name", .string "initializer-list"), ("inner", .array [])]])]}

private def coroutineBodyTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "c"), ("kind", .string "CoroutineBodyStmt"),
        ("name", .string "coroutine"), ("inner", .array [])]])]}

private def attributedStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "a"), ("kind", .string "AttributedStmt"),
        ("name", .string "attributed"), ("inner", .array [])]])]}

private def designatedInitializerTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "d"), ("kind", .string "DesignatedInitExpr"),
        ("name", .string "designated"), ("inner", .array [])]])]}

private def coreturnTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "c"), ("kind", .string "CoreturnStmt"),
        ("name", .string "co_return"), ("inner", .array [])]])]}

private def indirectGotoTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "g"), ("kind", .string "IndirectGotoStmt"),
        ("name", .string "goto"), ("inner", .array [])]])]}

private def capturedStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "c"), ("kind", .string "CapturedStmt"),
        ("name", .string "captured"), ("inner", .array [])]])]}

private def ompMetadirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPMetaDirective"),
        ("name", .string "metadirective"), ("inner", .array [])]])]}

private def ompTileDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTileDirective"),
        ("name", .string "tile"), ("inner", .array [])]])]}

private def ompStripeDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPStripeDirective"),
        ("name", .string "stripe"), ("inner", .array [])]])]}

private def ompUnrollDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPUnrollDirective"),
        ("name", .string "unroll"), ("inner", .array [])]])]}

private def ompReverseDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPReverseDirective"),
        ("name", .string "reverse"), ("inner", .array [])]])]}

private def ompInterchangeDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPInterchangeDirective"),
        ("name", .string "interchange"), ("inner", .array [])]])]}

private def ompDepobjDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPDepobjDirective"),
        ("name", .string "depobj"), ("inner", .array [])]])]}

private def ompScanDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPScanDirective"),
        ("name", .string "scan"), ("inner", .array [])]])]}

private def ompParallelDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPParallelDirective"),
        ("name", .string "parallel"), ("inner", .array [])]])]}

private def ompSimdDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPSimdDirective"),
        ("name", .string "simd"), ("inner", .array [])]])]}

private def ompForDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPForDirective"),
        ("name", .string "for"), ("inner", .array [])]])]}

private def ompForSimdDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPForSimdDirective"),
        ("name", .string "for-simd"), ("inner", .array [])]])]}

private def ompSectionsDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPSectionsDirective"),
        ("name", .string "sections"), ("inner", .array [])]])]}

private def ompSectionDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPSectionDirective"),
        ("name", .string "section"), ("inner", .array [])]])]}

private def ompSingleDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPSingleDirective"),
        ("name", .string "single"), ("inner", .array [])]])]}

private def ompMasterDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPMasterDirective"),
        ("name", .string "master"), ("inner", .array [])]])]}

private def ompCriticalDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPCriticalDirective"),
        ("name", .string "critical"), ("inner", .array [])]])]}

private def ompTaskDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTaskDirective"),
        ("name", .string "task"), ("inner", .array [])]])]}

private def ompTaskloopDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTaskloopDirective"),
        ("name", .string "taskloop"), ("inner", .array [])]])]}

private def ompTaskloopSimdDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTaskloopSimdDirective"),
        ("name", .string "taskloop-simd"), ("inner", .array [])]])]}

private def ompTeamsDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTeamsDirective"),
        ("name", .string "teams"), ("inner", .array [])]])]}

private def ompCancellationPointDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPCancellationPointDirective"),
        ("name", .string "cancellation-point"), ("inner", .array [])]])]}

private def ompCancelDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPCancelDirective"),
        ("name", .string "cancel"), ("inner", .array [])]])]}

private def ompScopeDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPScopeDirective"),
        ("name", .string "scope"), ("inner", .array [])]])]}

private def ompMaskedTaskLoopDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPMaskedTaskLoopDirective"),
        ("name", .string "masked-taskloop"), ("inner", .array [])]])]}

private def ompMaskedTaskLoopSimdDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPMaskedTaskLoopSimdDirective"),
        ("name", .string "masked-taskloop-simd"), ("inner", .array [])]])]}

private def ompParallelMaskedTaskLoopDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPParallelMaskedTaskLoopDirective"),
        ("name", .string "parallel-masked-taskloop"), ("inner", .array [])]])]}

private def ompParallelMaskedTaskLoopSimdDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPParallelMaskedTaskLoopSimdDirective"),
        ("name", .string "parallel-masked-taskloop-simd"), ("inner", .array [])]])]}

private def ompTeamsDistributeDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTeamsDistributeDirective"),
        ("name", .string "teams-distribute"), ("inner", .array [])]])]}

private def ompTeamsDistributeSimdDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTeamsDistributeSimdDirective"),
        ("name", .string "teams-distribute-simd"), ("inner", .array [])]])]}

private def ompTeamsDistributeParallelForDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTeamsDistributeParallelForDirective"),
        ("name", .string "teams-distribute-parallel-for"), ("inner", .array [])]])]}

private def ompTeamsDistributeParallelForSimdDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTeamsDistributeParallelForSimdDirective"),
        ("name", .string "teams-distribute-parallel-for-simd"), ("inner", .array [])]])]}

private def ompTargetDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTargetDirective"),
        ("name", .string "target"), ("inner", .array [])]])]}

private def ompTargetDataDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTargetDataDirective"),
        ("name", .string "target-data"), ("inner", .array [])]])]}

private def ompTargetEnterDataDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTargetEnterDataDirective"),
        ("name", .string "target-enter-data"), ("inner", .array [])]])]}

private def ompTargetExitDataDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTargetExitDataDirective"),
        ("name", .string "target-exit-data"), ("inner", .array [])]])]}

private def ompTargetParallelDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTargetParallelDirective"),
        ("name", .string "target-parallel"), ("inner", .array [])]])]}

private def ompTargetParallelForDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTargetParallelForDirective"),
        ("name", .string "target-parallel-for"), ("inner", .array [])]])]}

private def ompTargetParallelForSimdDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTargetParallelForSimdDirective"),
        ("name", .string "target-parallel-for-simd"), ("inner", .array [])]])]}

private def ompTargetSimdDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTargetSimdDirective"),
        ("name", .string "target-simd"), ("inner", .array [])]])]}

private def ompTargetUpdateDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTargetUpdateDirective"),
        ("name", .string "target-update"), ("inner", .array [])]])]}

private def ompDistributeDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPDistributeDirective"),
        ("name", .string "distribute"), ("inner", .array [])]])]}

private def ompDistributeParallelForDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPDistributeParallelForDirective"),
        ("name", .string "distribute-parallel-for"), ("inner", .array [])]])]}

private def ompDistributeParallelForSimdDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPDistributeParallelForSimdDirective"),
        ("name", .string "distribute-parallel-for-simd"), ("inner", .array [])]])]}

private def ompDistributeSimdDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPDistributeSimdDirective"),
        ("name", .string "distribute-simd"), ("inner", .array [])]])]}

private def ompParallelForDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPParallelForDirective"),
        ("name", .string "parallel-for"), ("inner", .array [])]])]}

private def ompParallelForSimdDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPParallelForSimdDirective"),
        ("name", .string "parallel-for-simd"), ("inner", .array [])]])]}

private def ompParallelSectionsDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPParallelSectionsDirective"),
        ("name", .string "parallel-sections"), ("inner", .array [])]])]}

private def ompParallelMasterDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPParallelMasterDirective"),
        ("name", .string "parallel-master"), ("inner", .array [])]])]}

private def ompOrderedDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPOrderedDirective"),
        ("name", .string "ordered"), ("inner", .array [])]])]}

private def ompAtomicDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPAtomicDirective"),
        ("name", .string "atomic"), ("inner", .array [])]])]}

private def ompFlushDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPFlushDirective"),
        ("name", .string "flush"), ("inner", .array [])]])]}

private def ompBarrierDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPBarrierDirective"),
        ("name", .string "barrier"), ("inner", .array [])]])]}

private def ompTaskwaitDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTaskwaitDirective"),
        ("name", .string "taskwait"), ("inner", .array [])]])]}

private def ompTaskgroupDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTaskgroupDirective"),
        ("name", .string "taskgroup"), ("inner", .array [])]])]}

private def ompMasterTaskloopDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPMasterTaskloopDirective"),
        ("name", .string "master-taskloop"), ("inner", .array [])]])]}

private def ompMasterTaskloopSimdDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPMasterTaskloopSimdDirective"),
        ("name", .string "master-taskloop-simd"), ("inner", .array [])]])]}

private def ompParallelMasterTaskloopDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPParallelMasterTaskloopDirective"),
        ("name", .string "parallel-master-taskloop"), ("inner", .array [])]])]}

private def ompParallelMasterTaskloopSimdDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPParallelMasterTaskloopSimdDirective"),
        ("name", .string "parallel-master-taskloop-simd"), ("inner", .array [])]])]}

private def ompTaskyieldDirectiveTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "OMPTaskyieldDirective"),
        ("name", .string "taskyield"), ("inner", .array [])]])]}

private def conditionalOperatorTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "c"), ("kind", .string "ConditionalOperator"),
        ("name", .string "select"), ("inner", .array [])]])]}

private def callTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "c"), ("kind", .string "CallExpr"),
        ("name", .string "call"), ("inner", .array [])]])]}

private def compoundAssignmentTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "a"), ("kind", .string "CompoundAssignOperator"),
        ("opcode", .string "+="), ("name", .string "add-assign"),
        ("inner", .array [])]])]}

private def lambdaTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "l"), ("kind", .string "LambdaExpr"),
        ("name", .string "lambda"), ("inner", .array [])]])]}

private def arraySubscriptTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "a"), ("kind", .string "ArraySubscriptExpr"),
        ("name", .string "subscript"), ("inner", .array [])]])]}

private def memberExpressionTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "m"), ("kind", .string "MemberExpr"),
        ("name", .string "value"), ("inner", .array [])]])]}

private def cxxMemberCallExpressionTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "c"), ("kind", .string "CXXMemberCallExpr"),
        ("name", .string "get"), ("inner", .array [])]])]}

private def cxxOperatorCallExpressionTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "o"), ("kind", .string "CXXOperatorCallExpr"),
        ("name", .string "operator+"), ("inner", .array [])]])]}

private def compoundStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "s"), ("kind", .string "CompoundStmt"),
        ("name", .string "block"), ("inner", .array [])]])]}

private def returnStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "r"), ("kind", .string "ReturnStmt"),
        ("name", .string "return"), ("inner", .array [])]])]}

private def ifStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "i"), ("kind", .string "IfStmt"),
        ("name", .string "if"), ("inner", .array [])]])]}

private def whileStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "w"), ("kind", .string "WhileStmt"),
        ("name", .string "while"), ("inner", .array [])]])]}

private def doStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "d"), ("kind", .string "DoStmt"),
        ("name", .string "do"), ("inner", .array [])]])]}

private def forStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "f"), ("kind", .string "ForStmt"),
        ("name", .string "for"), ("inner", .array [])]])]}

private def rangeForStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "r"), ("kind", .string "CXXForRangeStmt"),
        ("name", .string "range-for"), ("inner", .array [])]])]}

private def switchStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "s"), ("kind", .string "SwitchStmt"),
        ("name", .string "switch"), ("inner", .array [])]])]}

private def caseStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "c"), ("kind", .string "CaseStmt"),
        ("name", .string "case"), ("inner", .array [])]])]}

private def defaultStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "d"), ("kind", .string "DefaultStmt"),
        ("name", .string "default"), ("inner", .array [])]])]}

private def declarationStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "d"), ("kind", .string "DeclStmt"),
        ("name", .string "declaration"), ("inner", .array [])]])]}

private def breakStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "b"), ("kind", .string "BreakStmt"),
        ("name", .string "break"), ("inner", .array [])]])]}

private def continueStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "c"), ("kind", .string "ContinueStmt"),
        ("name", .string "continue"), ("inner", .array [])]])]}

private def nullStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "n"), ("kind", .string "NullStmt"),
        ("name", .string "null"), ("inner", .array [])]])]}

private def gotoStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "g"), ("kind", .string "GotoStmt"),
        ("name", .string "goto"), ("inner", .array [])]])]}

private def labelStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "l"), ("kind", .string "LabelStmt"),
        ("name", .string "done"), ("inner", .array [])]])]}

private def labelDeclarationTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "l"), ("kind", .string "LabelDecl"),
        ("name", .string "done"), ("inner", .array [])]])]}

private def cxxTryStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "t"), ("kind", .string "CXXTryStmt"),
        ("name", .string "try"), ("inner", .array [])]])]}

private def cxxCatchStatementTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "c"), ("kind", .string "CXXCatchStmt"),
        ("name", .string "catch"), ("inner", .array [])]])]}

private def cxxThrowExpressionTranslation : Artifact := {emptyTranslation with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "x"), ("kind", .string "CXXThrowExpr"),
        ("name", .string "throw"), ("inner", .array [])]])]}

def namespaceTranslationWitness : Bool :=
  (admitNamespaceDeclaration namespaceTranslation [0]).isOk

def functionTranslationWitness : Except String Unit :=
  admitFunctionDeclaration functionTranslation [0]

def parameterTranslationWitness : Except String Unit :=
  admitParameterDeclaration parameterTranslation [0, 0]

def recordTranslationWitness : Except String Unit :=
  admitRecordDeclaration recordTranslation [0]

def baseSpecifierTranslationWitness : Except String Unit :=
  admitBaseSpecifier baseSpecifierTranslation [0]

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

def nonTypeTemplateParameterTranslationWitness : Except String Unit :=
  admitNonTypeTemplateParameter templateParameterTranslation [0, 1]

def templateTemplateParameterTranslationWitness : Except String Unit :=
  admitTemplateTemplateParameter templateParameterTranslation [0, 2]

def classTemplateTranslationWitness : Except String Unit :=
  admitClassTemplateDeclaration templateParameterTranslation [0]

def functionTemplateTranslationWitness : Except String Unit :=
  admitFunctionTemplateDeclaration functionTemplateTranslation [0]

def variableTemplateTranslationWitness : Except String Unit :=
  admitVariableTemplateDeclaration variableTemplateTranslation [0]

def typeAliasTemplateTranslationWitness : Except String Unit :=
  admitTypeAliasTemplateDeclaration typeAliasTemplateTranslation [0]

def classTemplateSpecializationTranslationWitness : Except String Unit :=
  admitClassTemplateSpecializationDeclaration classTemplateSpecializationTranslation [0]

def variableTemplateSpecializationTranslationWitness : Except String Unit :=
  admitVariableTemplateSpecializationDeclaration variableTemplateSpecializationTranslation [0]

def classTemplatePartialSpecializationTranslationWitness : Except String Unit :=
  admitClassTemplatePartialSpecializationDeclaration classTemplatePartialSpecializationTranslation [0]

def variableTemplatePartialSpecializationTranslationWitness : Except String Unit :=
  admitVariableTemplatePartialSpecializationDeclaration variableTemplatePartialSpecializationTranslation [0]

def conceptTranslationWitness : Except String Unit :=
  admitConceptDeclaration conceptTranslation [0]

def deductionGuideTranslationWitness : Except String Unit :=
  admitDeductionGuideDeclaration deductionGuideTranslation [0]

def usingShadowTranslationWitness : Except String Unit :=
  admitUsingShadowDeclaration usingShadowTranslation [0]

def constructorUsingShadowTranslationWitness : Except String Unit :=
  admitConstructorUsingShadowDeclaration constructorUsingShadowTranslation [0]

def usingPackTranslationWitness : Except String Unit :=
  admitUsingPackDeclaration usingPackTranslation [0]

def unresolvedUsingTypenameTranslationWitness : Except String Unit :=
  admitUnresolvedUsingTypenameDeclaration unresolvedUsingTypenameTranslation [0]

def unresolvedUsingValueTranslationWitness : Except String Unit :=
  admitUnresolvedUsingValueDeclaration unresolvedUsingValueTranslation [0]

def bindingTranslationWitness : Except String Unit :=
  admitBindingDeclaration bindingTranslation [0]

def decompositionTranslationWitness : Except String Unit :=
  admitDecompositionDeclaration decompositionTranslation [0]

def indirectFieldTranslationWitness : Except String Unit :=
  admitIndirectFieldDeclaration indirectFieldTranslation [0]

def classScopeFunctionSpecializationTranslationWitness : Except String Unit :=
  admitClassScopeFunctionSpecializationDeclaration classScopeFunctionSpecializationTranslation [0]

def friendTemplateTranslationWitness : Except String Unit :=
  admitFriendTemplateDeclaration friendTemplateTranslation [0]

def templateParamObjectTranslationWitness : Except String Unit :=
  admitTemplateParamObjectDeclaration templateParamObjectTranslation [0]

def implicitConceptSpecializationTranslationWitness : Except String Unit :=
  admitImplicitConceptSpecializationDeclaration implicitConceptSpecializationTranslation [0]

def requiresExpressionTranslationWitness : Except String Unit :=
  admitRequiresExpression requiresExpressionTranslation [0]

def typeRequirementTranslationWitness : Except String Unit :=
  admitTypeRequirement typeRequirementTranslation [0]

def simpleRequirementTranslationWitness : Except String Unit :=
  admitSimpleRequirement simpleRequirementTranslation [0]

def compoundRequirementTranslationWitness : Except String Unit :=
  admitCompoundRequirement compoundRequirementTranslation [0]

def nestedRequirementTranslationWitness : Except String Unit :=
  admitNestedRequirement nestedRequirementTranslation [0]

def usingEnumTranslationWitness : Except String Unit :=
  admitUsingEnumDeclaration usingEnumTranslation [0]

def lifetimeExtendedTemporaryTranslationWitness : Except String Unit :=
  admitLifetimeExtendedTemporaryDeclaration lifetimeExtendedTemporaryTranslation [0]

def materializeTemporaryTranslationWitness : Except String Unit :=
  admitMaterializeTemporaryExpression materializeTemporaryTranslation [0]

def bindTemporaryTranslationWitness : Except String Unit :=
  admitCXXBindTemporaryExpression bindTemporaryTranslation [0]

def expressionWithCleanupsTranslationWitness : Except String Unit :=
  admitExpressionWithCleanups expressionWithCleanupsTranslation [0]

def temporaryObjectTranslationWitness : Except String Unit :=
  admitCXXTemporaryObjectExpression temporaryObjectTranslation [0]

def cxxConstructExpressionTranslationWitness : Except String Unit :=
  admitCXXConstructExpression cxxConstructExpressionTranslation [0]

def newTranslationWitness : Except String Unit :=
  admitCXXNewExpression newTranslation [0]

def deleteTranslationWitness : Except String Unit :=
  admitCXXDeleteExpression deleteTranslation [0]

def defaultInitTranslationWitness : Except String Unit :=
  admitCXXDefaultInitExpression defaultInitTranslation [0]

def scalarValueInitTranslationWitness : Except String Unit :=
  admitCXXScalarValueInitExpression scalarValueInitTranslation [0]

def initializerListTranslationWitness : Except String Unit :=
  admitInitializerListExpression initializerListTranslation [0]

def parenListInitTranslationWitness : Except String Unit :=
  admitCXXParenListInitExpression parenListInitTranslation [0]

def implicitValueInitTranslationWitness : Except String Unit :=
  admitImplicitValueInitExpression implicitValueInitTranslation [0]

def implicitCastTranslationWitness : Except String Unit :=
  admitImplicitCastExpression implicitCastTranslation [0]

def parenthesizedTranslationWitness : Except String Unit :=
  admitParenthesizedExpression parenthesizedTranslation [0]

def constantTranslationWitness : Except String Unit :=
  admitConstantExpression constantTranslation [0]

def staticCastTranslationWitness : Except String Unit :=
  admitCXXStaticCastExpression staticCastTranslation [0]

def constCastTranslationWitness : Except String Unit :=
  admitCXXConstCastExpression constCastTranslation [0]

def reinterpretCastTranslationWitness : Except String Unit :=
  admitCXXReinterpretCastExpression reinterpretCastTranslation [0]

def dynamicCastTranslationWitness : Except String Unit :=
  admitCXXDynamicCastExpression dynamicCastTranslation [0]

def boolLiteralTranslationWitness : Except String Unit :=
  admitCXXBoolLiteralExpression boolLiteralTranslation [0]

def nullPtrLiteralTranslationWitness : Except String Unit :=
  admitCXXNullPtrLiteralExpression nullPtrLiteralTranslation [0]

def characterLiteralTranslationWitness : Except String Unit :=
  admitCharacterLiteralExpression characterLiteralTranslation [0]

def floatingLiteralTranslationWitness : Except String Unit :=
  admitFloatingLiteralExpression floatingLiteralTranslation [0]

def stringLiteralTranslationWitness : Except String Unit :=
  admitStringLiteralExpression stringLiteralTranslation [0]

def integerLiteralTranslationWitness : Except String Unit :=
  admitIntegerLiteralExpression integerLiteralTranslation [0]

def declarationReferenceTranslationWitness : Except String Unit :=
  admitDeclarationReferenceExpression declarationReferenceTranslation [0]

def thisTranslationWitness : Except String Unit :=
  admitCXXThisExpression thisTranslation [0]

def unaryOperatorTranslationWitness : Except String Unit :=
  admitUnaryOperatorExpression unaryOperatorTranslation [0]

def binaryOperatorTranslationWitness : Except String Unit :=
  admitBinaryOperatorExpression binaryOperatorTranslation [0]

def cxxRewrittenBinaryOperatorTranslationWitness : Except String Unit :=
  admitCXXRewrittenBinaryOperatorExpression cxxRewrittenBinaryOperatorTranslation [0]

def cxxNoexceptTranslationWitness : Except String Unit :=
  admitCXXNoexceptExpression cxxNoexceptTranslation [0]

def cxxTypeidTranslationWitness : Except String Unit :=
  admitCXXTypeidExpression cxxTypeidTranslation [0]

def cxxFoldTranslationWitness : Except String Unit :=
  admitCXXFoldExpression cxxFoldTranslation [0]

def cxxCoawaitTranslationWitness : Except String Unit :=
  admitCXXCoawaitExpression cxxCoawaitTranslation [0]

def cStyleCastTranslationWitness : Except String Unit :=
  admitCStyleCastExpression cStyleCastTranslation [0]

def unaryExprOrTypeTraitTranslationWitness : Except String Unit :=
  admitUnaryExprOrTypeTraitExpression unaryExprOrTypeTraitTranslation [0]

def vaArgTranslationWitness : Except String Unit :=
  admitVAArgExpression vaArgTranslation [0]

def cxxDependentScopeMemberTranslationWitness : Except String Unit :=
  admitCXXDependentScopeMemberExpression cxxDependentScopeMemberTranslation [0]

def cxxDefaultArgumentTranslationWitness : Except String Unit :=
  admitCXXDefaultArgumentExpression cxxDefaultArgumentTranslation [0]

def cxxUnresolvedConstructTranslationWitness : Except String Unit :=
  admitCXXUnresolvedConstructExpression cxxUnresolvedConstructTranslation [0]

def unresolvedLookupTranslationWitness : Except String Unit :=
  admitUnresolvedLookupExpression unresolvedLookupTranslation [0]

def cxxPseudoDestructorTranslationWitness : Except String Unit :=
  admitCXXPseudoDestructorExpression cxxPseudoDestructorTranslation [0]

def cxxUnresolvedMemberTranslationWitness : Except String Unit :=
  admitCXXUnresolvedMemberExpression cxxUnresolvedMemberTranslation [0]

def cxxDependentScopeDeclRefTranslationWitness : Except String Unit :=
  admitCXXDependentScopeDeclRefExpression cxxDependentScopeDeclRefTranslation [0]

def cxxInheritedConstructorInitTranslationWitness : Except String Unit :=
  admitCXXInheritedConstructorInitExpression cxxInheritedConstructorInitTranslation [0]

def cxxStdInitializerListTranslationWitness : Except String Unit :=
  admitCXXStdInitializerListExpression cxxStdInitializerListTranslation [0]

def coroutineBodyTranslationWitness : Except String Unit :=
  admitCoroutineBodyStatement coroutineBodyTranslation [0]

def attributedStatementTranslationWitness : Except String Unit :=
  admitAttributedStatement attributedStatementTranslation [0]

def designatedInitializerTranslationWitness : Except String Unit :=
  admitDesignatedInitializerExpression designatedInitializerTranslation [0]

def coreturnTranslationWitness : Except String Unit :=
  admitCoreturnStatement coreturnTranslation [0]

def indirectGotoTranslationWitness : Except String Unit :=
  admitIndirectGotoStatement indirectGotoTranslation [0]

def capturedStatementTranslationWitness : Except String Unit :=
  admitCapturedStatement capturedStatementTranslation [0]

def ompMetadirectiveTranslationWitness : Except String Unit :=
  admitOMPMetadirective ompMetadirectiveTranslation [0]

def ompTileDirectiveTranslationWitness : Except String Unit :=
  admitOMPTileDirective ompTileDirectiveTranslation [0]

def ompStripeDirectiveTranslationWitness : Except String Unit :=
  admitOMPStripeDirective ompStripeDirectiveTranslation [0]

def ompUnrollDirectiveTranslationWitness : Except String Unit :=
  admitOMPUnrollDirective ompUnrollDirectiveTranslation [0]

def ompReverseDirectiveTranslationWitness : Except String Unit :=
  admitOMPReverseDirective ompReverseDirectiveTranslation [0]

def ompInterchangeDirectiveTranslationWitness : Except String Unit :=
  admitOMPInterchangeDirective ompInterchangeDirectiveTranslation [0]

def ompDepobjDirectiveTranslationWitness : Except String Unit :=
  admitOMPDepobjDirective ompDepobjDirectiveTranslation [0]

def ompScanDirectiveTranslationWitness : Except String Unit :=
  admitOMPScanDirective ompScanDirectiveTranslation [0]

def ompParallelDirectiveTranslationWitness : Except String Unit :=
  admitOMPParallelDirective ompParallelDirectiveTranslation [0]

def ompSimdDirectiveTranslationWitness : Except String Unit :=
  admitOMPSimdDirective ompSimdDirectiveTranslation [0]

def ompForDirectiveTranslationWitness : Except String Unit :=
  admitOMPForDirective ompForDirectiveTranslation [0]

def ompForSimdDirectiveTranslationWitness : Except String Unit :=
  admitOMPForSimdDirective ompForSimdDirectiveTranslation [0]

def ompSectionsDirectiveTranslationWitness : Except String Unit :=
  admitOMPSectionsDirective ompSectionsDirectiveTranslation [0]

def ompSectionDirectiveTranslationWitness : Except String Unit :=
  admitOMPSectionDirective ompSectionDirectiveTranslation [0]

def ompSingleDirectiveTranslationWitness : Except String Unit :=
  admitOMPSingleDirective ompSingleDirectiveTranslation [0]

def ompMasterDirectiveTranslationWitness : Except String Unit :=
  admitOMPMasterDirective ompMasterDirectiveTranslation [0]

def ompCriticalDirectiveTranslationWitness : Except String Unit :=
  admitOMPCriticalDirective ompCriticalDirectiveTranslation [0]

def ompTaskDirectiveTranslationWitness : Except String Unit :=
  admitOMPTaskDirective ompTaskDirectiveTranslation [0]

def ompTaskloopDirectiveTranslationWitness : Except String Unit :=
  admitOMPTaskloopDirective ompTaskloopDirectiveTranslation [0]

def ompTaskloopSimdDirectiveTranslationWitness : Except String Unit :=
  admitOMPTaskloopSimdDirective ompTaskloopSimdDirectiveTranslation [0]

def ompTeamsDirectiveTranslationWitness : Except String Unit :=
  admitOMPTeamsDirective ompTeamsDirectiveTranslation [0]

def ompCancellationPointDirectiveTranslationWitness : Except String Unit :=
  admitOMPCancellationPointDirective ompCancellationPointDirectiveTranslation [0]

def ompCancelDirectiveTranslationWitness : Except String Unit :=
  admitOMPCancelDirective ompCancelDirectiveTranslation [0]

def ompScopeDirectiveTranslationWitness : Except String Unit :=
  admitOMPScopeDirective ompScopeDirectiveTranslation [0]

def ompMaskedTaskLoopDirectiveTranslationWitness : Except String Unit :=
  admitOMPMaskedTaskLoopDirective ompMaskedTaskLoopDirectiveTranslation [0]

def ompMaskedTaskLoopSimdDirectiveTranslationWitness : Except String Unit :=
  admitOMPMaskedTaskLoopSimdDirective ompMaskedTaskLoopSimdDirectiveTranslation [0]

def ompParallelMaskedTaskLoopDirectiveTranslationWitness : Except String Unit :=
  admitOMPParallelMaskedTaskLoopDirective ompParallelMaskedTaskLoopDirectiveTranslation [0]

def ompParallelMaskedTaskLoopSimdDirectiveTranslationWitness : Except String Unit :=
  admitOMPParallelMaskedTaskLoopSimdDirective ompParallelMaskedTaskLoopSimdDirectiveTranslation [0]

def ompTeamsDistributeDirectiveTranslationWitness : Except String Unit :=
  admitOMPTeamsDistributeDirective ompTeamsDistributeDirectiveTranslation [0]

def ompTeamsDistributeSimdDirectiveTranslationWitness : Except String Unit :=
  admitOMPTeamsDistributeSimdDirective ompTeamsDistributeSimdDirectiveTranslation [0]

def ompTeamsDistributeParallelForDirectiveTranslationWitness : Except String Unit :=
  admitOMPTeamsDistributeParallelForDirective ompTeamsDistributeParallelForDirectiveTranslation [0]

def ompTeamsDistributeParallelForSimdDirectiveTranslationWitness : Except String Unit :=
  admitOMPTeamsDistributeParallelForSimdDirective ompTeamsDistributeParallelForSimdDirectiveTranslation [0]

def ompTargetDirectiveTranslationWitness : Except String Unit :=
  admitOMPTargetDirective ompTargetDirectiveTranslation [0]

def ompTargetDataDirectiveTranslationWitness : Except String Unit :=
  admitOMPTargetDataDirective ompTargetDataDirectiveTranslation [0]

def ompTargetEnterDataDirectiveTranslationWitness : Except String Unit :=
  admitOMPTargetEnterDataDirective ompTargetEnterDataDirectiveTranslation [0]

def ompTargetExitDataDirectiveTranslationWitness : Except String Unit :=
  admitOMPTargetExitDataDirective ompTargetExitDataDirectiveTranslation [0]

def ompTargetParallelDirectiveTranslationWitness : Except String Unit :=
  admitOMPTargetParallelDirective ompTargetParallelDirectiveTranslation [0]

def ompTargetParallelForDirectiveTranslationWitness : Except String Unit :=
  admitOMPTargetParallelForDirective ompTargetParallelForDirectiveTranslation [0]

def ompTargetParallelForSimdDirectiveTranslationWitness : Except String Unit :=
  admitOMPTargetParallelForSimdDirective ompTargetParallelForSimdDirectiveTranslation [0]

def ompTargetSimdDirectiveTranslationWitness : Except String Unit :=
  admitOMPTargetSimdDirective ompTargetSimdDirectiveTranslation [0]

def ompTargetUpdateDirectiveTranslationWitness : Except String Unit :=
  admitOMPTargetUpdateDirective ompTargetUpdateDirectiveTranslation [0]

def ompDistributeDirectiveTranslationWitness : Except String Unit :=
  admitOMPDistributeDirective ompDistributeDirectiveTranslation [0]

def ompDistributeParallelForDirectiveTranslationWitness : Except String Unit :=
  admitOMPDistributeParallelForDirective ompDistributeParallelForDirectiveTranslation [0]

def ompDistributeParallelForSimdDirectiveTranslationWitness : Except String Unit :=
  admitOMPDistributeParallelForSimdDirective ompDistributeParallelForSimdDirectiveTranslation [0]

def ompDistributeSimdDirectiveTranslationWitness : Except String Unit :=
  admitOMPDistributeSimdDirective ompDistributeSimdDirectiveTranslation [0]

def ompParallelForDirectiveTranslationWitness : Except String Unit :=
  admitOMPParallelForDirective ompParallelForDirectiveTranslation [0]

def ompParallelForSimdDirectiveTranslationWitness : Except String Unit :=
  admitOMPParallelForSimdDirective ompParallelForSimdDirectiveTranslation [0]

def ompParallelSectionsDirectiveTranslationWitness : Except String Unit :=
  admitOMPParallelSectionsDirective ompParallelSectionsDirectiveTranslation [0]

def ompParallelMasterDirectiveTranslationWitness : Except String Unit :=
  admitOMPParallelMasterDirective ompParallelMasterDirectiveTranslation [0]

def ompOrderedDirectiveTranslationWitness : Except String Unit :=
  admitOMPOrderedDirective ompOrderedDirectiveTranslation [0]

def ompAtomicDirectiveTranslationWitness : Except String Unit :=
  admitOMPAtomicDirective ompAtomicDirectiveTranslation [0]

def ompFlushDirectiveTranslationWitness : Except String Unit :=
  admitOMPFlushDirective ompFlushDirectiveTranslation [0]

def ompBarrierDirectiveTranslationWitness : Except String Unit :=
  admitOMPBarrierDirective ompBarrierDirectiveTranslation [0]

def ompTaskwaitDirectiveTranslationWitness : Except String Unit :=
  admitOMPTaskwaitDirective ompTaskwaitDirectiveTranslation [0]

def ompTaskgroupDirectiveTranslationWitness : Except String Unit :=
  admitOMPTaskgroupDirective ompTaskgroupDirectiveTranslation [0]

def ompMasterTaskloopDirectiveTranslationWitness : Except String Unit :=
  admitOMPMasterTaskloopDirective ompMasterTaskloopDirectiveTranslation [0]

def ompMasterTaskloopSimdDirectiveTranslationWitness : Except String Unit :=
  admitOMPMasterTaskloopSimdDirective ompMasterTaskloopSimdDirectiveTranslation [0]

def ompParallelMasterTaskloopDirectiveTranslationWitness : Except String Unit :=
  admitOMPParallelMasterTaskloopDirective ompParallelMasterTaskloopDirectiveTranslation [0]

def ompParallelMasterTaskloopSimdDirectiveTranslationWitness : Except String Unit :=
  admitOMPParallelMasterTaskloopSimdDirective ompParallelMasterTaskloopSimdDirectiveTranslation [0]

def ompTaskyieldDirectiveTranslationWitness : Except String Unit :=
  admitOMPTaskyieldDirective ompTaskyieldDirectiveTranslation [0]

def conditionalOperatorTranslationWitness : Except String Unit :=
  admitConditionalOperatorExpression conditionalOperatorTranslation [0]

def callTranslationWitness : Except String Unit :=
  admitCallExpression callTranslation [0]

def compoundAssignmentTranslationWitness : Except String Unit :=
  admitCompoundAssignmentOperator compoundAssignmentTranslation [0]

def lambdaTranslationWitness : Except String Unit :=
  admitLambdaExpression lambdaTranslation [0]

def arraySubscriptTranslationWitness : Except String Unit :=
  admitArraySubscriptExpression arraySubscriptTranslation [0]

def memberExpressionTranslationWitness : Except String Unit :=
  admitMemberExpression memberExpressionTranslation [0]

def cxxMemberCallExpressionTranslationWitness : Except String Unit :=
  admitCXXMemberCallExpression cxxMemberCallExpressionTranslation [0]

def cxxOperatorCallExpressionTranslationWitness : Except String Unit :=
  admitCXXOperatorCallExpression cxxOperatorCallExpressionTranslation [0]

def compoundStatementTranslationWitness : Except String Unit :=
  admitCompoundStatement compoundStatementTranslation [0]

def returnStatementTranslationWitness : Except String Unit :=
  admitReturnStatement returnStatementTranslation [0]

def ifStatementTranslationWitness : Except String Unit :=
  admitIfStatement ifStatementTranslation [0]

def whileStatementTranslationWitness : Except String Unit :=
  admitWhileStatement whileStatementTranslation [0]

def doStatementTranslationWitness : Except String Unit :=
  admitDoStatement doStatementTranslation [0]

def forStatementTranslationWitness : Except String Unit :=
  admitForStatement forStatementTranslation [0]

def rangeForStatementTranslationWitness : Except String Unit :=
  admitRangeForStatement rangeForStatementTranslation [0]

def switchStatementTranslationWitness : Except String Unit :=
  admitSwitchStatement switchStatementTranslation [0]

def caseStatementTranslationWitness : Except String Unit :=
  admitCaseStatement caseStatementTranslation [0]

def defaultStatementTranslationWitness : Except String Unit :=
  admitDefaultStatement defaultStatementTranslation [0]

def declarationStatementTranslationWitness : Except String Unit :=
  admitDeclarationStatement declarationStatementTranslation [0]

def breakStatementTranslationWitness : Except String Unit :=
  admitBreakStatement breakStatementTranslation [0]

def continueStatementTranslationWitness : Except String Unit :=
  admitContinueStatement continueStatementTranslation [0]

def nullStatementTranslationWitness : Except String Unit :=
  admitNullStatement nullStatementTranslation [0]

def gotoStatementTranslationWitness : Except String Unit :=
  admitGotoStatement gotoStatementTranslation [0]

def labelStatementTranslationWitness : Except String Unit :=
  admitLabelStatement labelStatementTranslation [0]

def labelDeclarationTranslationWitness : Except String Unit :=
  admitLabelDeclaration labelDeclarationTranslation [0]

def cxxTryStatementTranslationWitness : Except String Unit :=
  admitCXXTryStatement cxxTryStatementTranslation [0]

def cxxCatchStatementTranslationWitness : Except String Unit :=
  admitCXXCatchStatement cxxCatchStatementTranslation [0]

def cxxThrowExpressionTranslationWitness : Except String Unit :=
  admitCXXThrowExpression cxxThrowExpressionTranslation [0]

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
#guard baseSpecifierTranslationWitness matches .ok ()
#guard admitBaseSpecifier baseSpecifierTranslation [] matches .error _
#guard admitBaseSpecifier functionTranslation [0] matches .error _
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
#guard nonTypeTemplateParameterTranslationWitness matches .ok ()
#guard admitNonTypeTemplateParameter templateParameterTranslation [] matches .error _
#guard admitNonTypeTemplateParameter functionTranslation [0] matches .error _
#guard templateTemplateParameterTranslationWitness matches .ok ()
#guard admitTemplateTemplateParameter templateParameterTranslation [] matches .error _
#guard admitTemplateTemplateParameter functionTranslation [0] matches .error _
#guard classTemplateTranslationWitness matches .ok ()
#guard admitClassTemplateDeclaration templateParameterTranslation [] matches .error _
#guard admitClassTemplateDeclaration functionTranslation [0] matches .error _
#guard functionTemplateTranslationWitness matches .ok ()
#guard admitFunctionTemplateDeclaration functionTemplateTranslation [] matches .error _
#guard admitFunctionTemplateDeclaration functionTranslation [0] matches .error _
#guard variableTemplateTranslationWitness matches .ok ()
#guard admitVariableTemplateDeclaration variableTemplateTranslation [] matches .error _
#guard admitVariableTemplateDeclaration functionTranslation [0] matches .error _
#guard typeAliasTemplateTranslationWitness matches .ok ()
#guard admitTypeAliasTemplateDeclaration typeAliasTemplateTranslation [] matches .error _
#guard admitTypeAliasTemplateDeclaration functionTranslation [0] matches .error _
#guard classTemplateSpecializationTranslationWitness matches .ok ()
#guard admitClassTemplateSpecializationDeclaration classTemplateSpecializationTranslation [] matches .error _
#guard admitClassTemplateSpecializationDeclaration functionTranslation [0] matches .error _
#guard variableTemplateSpecializationTranslationWitness matches .ok ()
#guard admitVariableTemplateSpecializationDeclaration variableTemplateSpecializationTranslation [] matches .error _
#guard admitVariableTemplateSpecializationDeclaration functionTranslation [0] matches .error _
#guard classTemplatePartialSpecializationTranslationWitness matches .ok ()
#guard admitClassTemplatePartialSpecializationDeclaration classTemplatePartialSpecializationTranslation [] matches .error _
#guard admitClassTemplatePartialSpecializationDeclaration functionTranslation [0] matches .error _
#guard variableTemplatePartialSpecializationTranslationWitness matches .ok ()
#guard admitVariableTemplatePartialSpecializationDeclaration variableTemplatePartialSpecializationTranslation [] matches .error _
#guard admitVariableTemplatePartialSpecializationDeclaration functionTranslation [0] matches .error _
#guard conceptTranslationWitness matches .ok ()
#guard admitConceptDeclaration conceptTranslation [] matches .error _
#guard admitConceptDeclaration functionTranslation [0] matches .error _
#guard deductionGuideTranslationWitness matches .ok ()
#guard admitDeductionGuideDeclaration deductionGuideTranslation [] matches .error _
#guard admitDeductionGuideDeclaration functionTranslation [0] matches .error _
#guard usingShadowTranslationWitness matches .ok ()
#guard admitUsingShadowDeclaration usingShadowTranslation [] matches .error _
#guard admitUsingShadowDeclaration functionTranslation [0] matches .error _
#guard constructorUsingShadowTranslationWitness matches .ok ()
#guard admitConstructorUsingShadowDeclaration constructorUsingShadowTranslation [] matches .error _
#guard admitConstructorUsingShadowDeclaration functionTranslation [0] matches .error _
#guard usingPackTranslationWitness matches .ok ()
#guard admitUsingPackDeclaration usingPackTranslation [] matches .error _
#guard admitUsingPackDeclaration functionTranslation [0] matches .error _
#guard unresolvedUsingTypenameTranslationWitness matches .ok ()
#guard admitUnresolvedUsingTypenameDeclaration unresolvedUsingTypenameTranslation [] matches .error _
#guard admitUnresolvedUsingTypenameDeclaration functionTranslation [0] matches .error _
#guard unresolvedUsingValueTranslationWitness matches .ok ()
#guard admitUnresolvedUsingValueDeclaration unresolvedUsingValueTranslation [] matches .error _
#guard admitUnresolvedUsingValueDeclaration functionTranslation [0] matches .error _
#guard bindingTranslationWitness matches .ok ()
#guard admitBindingDeclaration bindingTranslation [] matches .error _
#guard admitBindingDeclaration functionTranslation [0] matches .error _
#guard decompositionTranslationWitness matches .ok ()
#guard admitDecompositionDeclaration decompositionTranslation [] matches .error _
#guard admitDecompositionDeclaration functionTranslation [0] matches .error _
#guard indirectFieldTranslationWitness matches .ok ()
#guard admitIndirectFieldDeclaration indirectFieldTranslation [] matches .error _
#guard admitIndirectFieldDeclaration functionTranslation [0] matches .error _
#guard classScopeFunctionSpecializationTranslationWitness matches .ok ()
#guard admitClassScopeFunctionSpecializationDeclaration classScopeFunctionSpecializationTranslation [] matches .error _
#guard admitClassScopeFunctionSpecializationDeclaration functionTranslation [0] matches .error _
#guard friendTemplateTranslationWitness matches .ok ()
#guard admitFriendTemplateDeclaration friendTemplateTranslation [] matches .error _
#guard admitFriendTemplateDeclaration functionTranslation [0] matches .error _
#guard templateParamObjectTranslationWitness matches .ok ()
#guard admitTemplateParamObjectDeclaration templateParamObjectTranslation [] matches .error _
#guard admitTemplateParamObjectDeclaration functionTranslation [0] matches .error _
#guard implicitConceptSpecializationTranslationWitness matches .ok ()
#guard admitImplicitConceptSpecializationDeclaration implicitConceptSpecializationTranslation [] matches .error _
#guard admitImplicitConceptSpecializationDeclaration functionTranslation [0] matches .error _
#guard requiresExpressionTranslationWitness matches .ok ()
#guard admitRequiresExpression requiresExpressionTranslation [] matches .error _
#guard admitRequiresExpression functionTranslation [0] matches .error _
#guard typeRequirementTranslationWitness matches .ok ()
#guard admitTypeRequirement typeRequirementTranslation [] matches .error _
#guard admitTypeRequirement functionTranslation [0] matches .error _
#guard simpleRequirementTranslationWitness matches .ok ()
#guard admitSimpleRequirement simpleRequirementTranslation [] matches .error _
#guard admitSimpleRequirement functionTranslation [0] matches .error _
#guard compoundRequirementTranslationWitness matches .ok ()
#guard admitCompoundRequirement compoundRequirementTranslation [] matches .error _
#guard admitCompoundRequirement functionTranslation [0] matches .error _
#guard nestedRequirementTranslationWitness matches .ok ()
#guard admitNestedRequirement nestedRequirementTranslation [] matches .error _
#guard admitNestedRequirement functionTranslation [0] matches .error _
#guard usingEnumTranslationWitness matches .ok ()
#guard admitUsingEnumDeclaration usingEnumTranslation [] matches .error _
#guard admitUsingEnumDeclaration functionTranslation [0] matches .error _
#guard lifetimeExtendedTemporaryTranslationWitness matches .ok ()
#guard admitLifetimeExtendedTemporaryDeclaration lifetimeExtendedTemporaryTranslation [] matches .error _
#guard admitLifetimeExtendedTemporaryDeclaration functionTranslation [0] matches .error _
#guard materializeTemporaryTranslationWitness matches .ok ()
#guard admitMaterializeTemporaryExpression materializeTemporaryTranslation [] matches .error _
#guard admitMaterializeTemporaryExpression functionTranslation [0] matches .error _
#guard bindTemporaryTranslationWitness matches .ok ()
#guard admitCXXBindTemporaryExpression bindTemporaryTranslation [] matches .error _
#guard admitCXXBindTemporaryExpression functionTranslation [0] matches .error _
#guard expressionWithCleanupsTranslationWitness matches .ok ()
#guard admitExpressionWithCleanups expressionWithCleanupsTranslation [] matches .error _
#guard admitExpressionWithCleanups functionTranslation [0] matches .error _
#guard temporaryObjectTranslationWitness matches .ok ()
#guard admitCXXTemporaryObjectExpression temporaryObjectTranslation [] matches .error _
#guard admitCXXTemporaryObjectExpression functionTranslation [0] matches .error _
#guard cxxConstructExpressionTranslationWitness matches .ok ()
#guard admitCXXConstructExpression cxxConstructExpressionTranslation [] matches .error _
#guard admitCXXConstructExpression functionTranslation [0] matches .error _
#guard newTranslationWitness matches .ok ()
#guard admitCXXNewExpression newTranslation [] matches .error _
#guard admitCXXNewExpression functionTranslation [0] matches .error _
#guard deleteTranslationWitness matches .ok ()
#guard admitCXXDeleteExpression deleteTranslation [] matches .error _
#guard admitCXXDeleteExpression functionTranslation [0] matches .error _
#guard defaultInitTranslationWitness matches .ok ()
#guard admitCXXDefaultInitExpression defaultInitTranslation [] matches .error _
#guard admitCXXDefaultInitExpression functionTranslation [0] matches .error _
#guard scalarValueInitTranslationWitness matches .ok ()
#guard admitCXXScalarValueInitExpression scalarValueInitTranslation [] matches .error _
#guard admitCXXScalarValueInitExpression functionTranslation [0] matches .error _
#guard initializerListTranslationWitness matches .ok ()
#guard admitInitializerListExpression initializerListTranslation [] matches .error _
#guard admitInitializerListExpression functionTranslation [0] matches .error _
#guard parenListInitTranslationWitness matches .ok ()
#guard admitCXXParenListInitExpression parenListInitTranslation [] matches .error _
#guard admitCXXParenListInitExpression functionTranslation [0] matches .error _
#guard implicitValueInitTranslationWitness matches .ok ()
#guard admitImplicitValueInitExpression implicitValueInitTranslation [] matches .error _
#guard admitImplicitValueInitExpression functionTranslation [0] matches .error _
#guard implicitCastTranslationWitness matches .ok ()
#guard admitImplicitCastExpression implicitCastTranslation [] matches .error _
#guard admitImplicitCastExpression functionTranslation [0] matches .error _
#guard parenthesizedTranslationWitness matches .ok ()
#guard admitParenthesizedExpression parenthesizedTranslation [] matches .error _
#guard admitParenthesizedExpression functionTranslation [0] matches .error _
#guard constantTranslationWitness matches .ok ()
#guard admitConstantExpression constantTranslation [] matches .error _
#guard admitConstantExpression functionTranslation [0] matches .error _
#guard staticCastTranslationWitness matches .ok ()
#guard admitCXXStaticCastExpression staticCastTranslation [] matches .error _
#guard admitCXXStaticCastExpression functionTranslation [0] matches .error _
#guard constCastTranslationWitness matches .ok ()
#guard admitCXXConstCastExpression constCastTranslation [] matches .error _
#guard admitCXXConstCastExpression functionTranslation [0] matches .error _
#guard reinterpretCastTranslationWitness matches .ok ()
#guard admitCXXReinterpretCastExpression reinterpretCastTranslation [] matches .error _
#guard admitCXXReinterpretCastExpression functionTranslation [0] matches .error _
#guard dynamicCastTranslationWitness matches .ok ()
#guard admitCXXDynamicCastExpression dynamicCastTranslation [] matches .error _
#guard admitCXXDynamicCastExpression functionTranslation [0] matches .error _
#guard boolLiteralTranslationWitness matches .ok ()
#guard admitCXXBoolLiteralExpression boolLiteralTranslation [] matches .error _
#guard admitCXXBoolLiteralExpression functionTranslation [0] matches .error _
#guard nullPtrLiteralTranslationWitness matches .ok ()
#guard admitCXXNullPtrLiteralExpression nullPtrLiteralTranslation [] matches .error _
#guard admitCXXNullPtrLiteralExpression functionTranslation [0] matches .error _
#guard characterLiteralTranslationWitness matches .ok ()
#guard admitCharacterLiteralExpression characterLiteralTranslation [] matches .error _
#guard admitCharacterLiteralExpression functionTranslation [0] matches .error _
#guard floatingLiteralTranslationWitness matches .ok ()
#guard admitFloatingLiteralExpression floatingLiteralTranslation [] matches .error _
#guard admitFloatingLiteralExpression functionTranslation [0] matches .error _
#guard stringLiteralTranslationWitness matches .ok ()
#guard admitStringLiteralExpression stringLiteralTranslation [] matches .error _
#guard admitStringLiteralExpression functionTranslation [0] matches .error _
#guard integerLiteralTranslationWitness matches .ok ()
#guard admitIntegerLiteralExpression integerLiteralTranslation [] matches .error _
#guard admitIntegerLiteralExpression functionTranslation [0] matches .error _
#guard declarationReferenceTranslationWitness matches .ok ()
#guard admitDeclarationReferenceExpression declarationReferenceTranslation [] matches .error _
#guard admitDeclarationReferenceExpression functionTranslation [0] matches .error _
#guard thisTranslationWitness matches .ok ()
#guard admitCXXThisExpression thisTranslation [] matches .error _
#guard admitCXXThisExpression functionTranslation [0] matches .error _
#guard unaryOperatorTranslationWitness matches .ok ()
#guard admitUnaryOperatorExpression unaryOperatorTranslation [] matches .error _
#guard admitUnaryOperatorExpression functionTranslation [0] matches .error _
#guard binaryOperatorTranslationWitness matches .ok ()
#guard admitBinaryOperatorExpression binaryOperatorTranslation [] matches .error _
#guard admitBinaryOperatorExpression functionTranslation [0] matches .error _
#guard cxxRewrittenBinaryOperatorTranslationWitness matches .ok ()
#guard admitCXXRewrittenBinaryOperatorExpression cxxRewrittenBinaryOperatorTranslation [] matches .error _
#guard admitCXXRewrittenBinaryOperatorExpression functionTranslation [0] matches .error _
#guard cxxNoexceptTranslationWitness matches .ok ()
#guard admitCXXNoexceptExpression cxxNoexceptTranslation [] matches .error _
#guard admitCXXNoexceptExpression functionTranslation [0] matches .error _
#guard cxxTypeidTranslationWitness matches .ok ()
#guard admitCXXTypeidExpression cxxTypeidTranslation [] matches .error _
#guard admitCXXTypeidExpression functionTranslation [0] matches .error _
#guard cxxFoldTranslationWitness matches .ok ()
#guard admitCXXFoldExpression cxxFoldTranslation [] matches .error _
#guard admitCXXFoldExpression functionTranslation [0] matches .error _
#guard cxxCoawaitTranslationWitness matches .ok ()
#guard admitCXXCoawaitExpression cxxCoawaitTranslation [] matches .error _
#guard admitCXXCoawaitExpression functionTranslation [0] matches .error _
#guard cStyleCastTranslationWitness matches .ok ()
#guard admitCStyleCastExpression cStyleCastTranslation [] matches .error _
#guard admitCStyleCastExpression functionTranslation [0] matches .error _
#guard unaryExprOrTypeTraitTranslationWitness matches .ok ()
#guard admitUnaryExprOrTypeTraitExpression unaryExprOrTypeTraitTranslation [] matches .error _
#guard admitUnaryExprOrTypeTraitExpression functionTranslation [0] matches .error _
#guard vaArgTranslationWitness matches .ok ()
#guard admitVAArgExpression vaArgTranslation [] matches .error _
#guard admitVAArgExpression functionTranslation [0] matches .error _
#guard cxxDependentScopeMemberTranslationWitness matches .ok ()
#guard admitCXXDependentScopeMemberExpression cxxDependentScopeMemberTranslation [] matches .error _
#guard admitCXXDependentScopeMemberExpression functionTranslation [0] matches .error _
#guard cxxDefaultArgumentTranslationWitness matches .ok ()
#guard admitCXXDefaultArgumentExpression cxxDefaultArgumentTranslation [] matches .error _
#guard admitCXXDefaultArgumentExpression functionTranslation [0] matches .error _
#guard cxxUnresolvedConstructTranslationWitness matches .ok ()
#guard admitCXXUnresolvedConstructExpression cxxUnresolvedConstructTranslation [] matches .error _
#guard admitCXXUnresolvedConstructExpression functionTranslation [0] matches .error _
#guard unresolvedLookupTranslationWitness matches .ok ()
#guard admitUnresolvedLookupExpression unresolvedLookupTranslation [] matches .error _
#guard admitUnresolvedLookupExpression functionTranslation [0] matches .error _
#guard cxxPseudoDestructorTranslationWitness matches .ok ()
#guard admitCXXPseudoDestructorExpression cxxPseudoDestructorTranslation [] matches .error _
#guard admitCXXPseudoDestructorExpression functionTranslation [0] matches .error _
#guard cxxUnresolvedMemberTranslationWitness matches .ok ()
#guard admitCXXUnresolvedMemberExpression cxxUnresolvedMemberTranslation [] matches .error _
#guard admitCXXUnresolvedMemberExpression functionTranslation [0] matches .error _
#guard cxxDependentScopeDeclRefTranslationWitness matches .ok ()
#guard admitCXXDependentScopeDeclRefExpression cxxDependentScopeDeclRefTranslation [] matches .error _
#guard admitCXXDependentScopeDeclRefExpression functionTranslation [0] matches .error _
#guard cxxInheritedConstructorInitTranslationWitness matches .ok ()
#guard admitCXXInheritedConstructorInitExpression cxxInheritedConstructorInitTranslation [] matches .error _
#guard admitCXXInheritedConstructorInitExpression functionTranslation [0] matches .error _
#guard cxxStdInitializerListTranslationWitness matches .ok ()
#guard admitCXXStdInitializerListExpression cxxStdInitializerListTranslation [] matches .error _
#guard admitCXXStdInitializerListExpression functionTranslation [0] matches .error _
#guard coroutineBodyTranslationWitness matches .ok ()
#guard admitCoroutineBodyStatement coroutineBodyTranslation [] matches .error _
#guard admitCoroutineBodyStatement functionTranslation [0] matches .error _
#guard attributedStatementTranslationWitness matches .ok ()
#guard admitAttributedStatement attributedStatementTranslation [] matches .error _
#guard admitAttributedStatement functionTranslation [0] matches .error _
#guard designatedInitializerTranslationWitness matches .ok ()
#guard admitDesignatedInitializerExpression designatedInitializerTranslation [] matches .error _
#guard admitDesignatedInitializerExpression functionTranslation [0] matches .error _
#guard coreturnTranslationWitness matches .ok ()
#guard admitCoreturnStatement coreturnTranslation [] matches .error _
#guard admitCoreturnStatement functionTranslation [0] matches .error _
#guard indirectGotoTranslationWitness matches .ok ()
#guard admitIndirectGotoStatement indirectGotoTranslation [] matches .error _
#guard admitIndirectGotoStatement functionTranslation [0] matches .error _
#guard capturedStatementTranslationWitness matches .ok ()
#guard admitCapturedStatement capturedStatementTranslation [] matches .error _
#guard admitCapturedStatement functionTranslation [0] matches .error _
#guard ompMetadirectiveTranslationWitness matches .ok ()
#guard admitOMPMetadirective ompMetadirectiveTranslation [] matches .error _
#guard admitOMPMetadirective functionTranslation [0] matches .error _
#guard ompTileDirectiveTranslationWitness matches .ok ()
#guard admitOMPTileDirective ompTileDirectiveTranslation [] matches .error _
#guard admitOMPTileDirective functionTranslation [0] matches .error _
#guard ompStripeDirectiveTranslationWitness matches .ok ()
#guard admitOMPStripeDirective ompStripeDirectiveTranslation [] matches .error _
#guard admitOMPStripeDirective functionTranslation [0] matches .error _
#guard ompUnrollDirectiveTranslationWitness matches .ok ()
#guard admitOMPUnrollDirective ompUnrollDirectiveTranslation [] matches .error _
#guard admitOMPUnrollDirective functionTranslation [0] matches .error _
#guard ompReverseDirectiveTranslationWitness matches .ok ()
#guard admitOMPReverseDirective ompReverseDirectiveTranslation [] matches .error _
#guard admitOMPReverseDirective functionTranslation [0] matches .error _
#guard ompInterchangeDirectiveTranslationWitness matches .ok ()
#guard admitOMPInterchangeDirective ompInterchangeDirectiveTranslation [] matches .error _
#guard admitOMPInterchangeDirective functionTranslation [0] matches .error _
#guard ompDepobjDirectiveTranslationWitness matches .ok ()
#guard admitOMPDepobjDirective ompDepobjDirectiveTranslation [] matches .error _
#guard admitOMPDepobjDirective functionTranslation [0] matches .error _
#guard ompScanDirectiveTranslationWitness matches .ok ()
#guard admitOMPScanDirective ompScanDirectiveTranslation [] matches .error _
#guard admitOMPScanDirective functionTranslation [0] matches .error _
#guard ompParallelDirectiveTranslationWitness matches .ok ()
#guard admitOMPParallelDirective ompParallelDirectiveTranslation [] matches .error _
#guard admitOMPParallelDirective functionTranslation [0] matches .error _
#guard ompSimdDirectiveTranslationWitness matches .ok ()
#guard admitOMPSimdDirective ompSimdDirectiveTranslation [] matches .error _
#guard admitOMPSimdDirective functionTranslation [0] matches .error _
#guard ompForDirectiveTranslationWitness matches .ok ()
#guard admitOMPForDirective ompForDirectiveTranslation [] matches .error _
#guard admitOMPForDirective functionTranslation [0] matches .error _
#guard ompForSimdDirectiveTranslationWitness matches .ok ()
#guard admitOMPForSimdDirective ompForSimdDirectiveTranslation [] matches .error _
#guard admitOMPForSimdDirective functionTranslation [0] matches .error _
#guard ompSectionsDirectiveTranslationWitness matches .ok ()
#guard admitOMPSectionsDirective ompSectionsDirectiveTranslation [] matches .error _
#guard admitOMPSectionsDirective functionTranslation [0] matches .error _
#guard ompSectionDirectiveTranslationWitness matches .ok ()
#guard admitOMPSectionDirective ompSectionDirectiveTranslation [] matches .error _
#guard admitOMPSectionDirective functionTranslation [0] matches .error _
#guard ompSingleDirectiveTranslationWitness matches .ok ()
#guard admitOMPSingleDirective ompSingleDirectiveTranslation [] matches .error _
#guard admitOMPSingleDirective functionTranslation [0] matches .error _
#guard ompMasterDirectiveTranslationWitness matches .ok ()
#guard admitOMPMasterDirective ompMasterDirectiveTranslation [] matches .error _
#guard admitOMPMasterDirective functionTranslation [0] matches .error _
#guard ompCriticalDirectiveTranslationWitness matches .ok ()
#guard admitOMPCriticalDirective ompCriticalDirectiveTranslation [] matches .error _
#guard admitOMPCriticalDirective functionTranslation [0] matches .error _
#guard ompTaskDirectiveTranslationWitness matches .ok ()
#guard admitOMPTaskDirective ompTaskDirectiveTranslation [] matches .error _
#guard admitOMPTaskDirective functionTranslation [0] matches .error _
#guard ompTaskloopDirectiveTranslationWitness matches .ok ()
#guard admitOMPTaskloopDirective ompTaskloopDirectiveTranslation [] matches .error _
#guard admitOMPTaskloopDirective functionTranslation [0] matches .error _
#guard ompTaskloopSimdDirectiveTranslationWitness matches .ok ()
#guard admitOMPTaskloopSimdDirective ompTaskloopSimdDirectiveTranslation [] matches .error _
#guard admitOMPTaskloopSimdDirective functionTranslation [0] matches .error _
#guard ompTeamsDirectiveTranslationWitness matches .ok ()
#guard admitOMPTeamsDirective ompTeamsDirectiveTranslation [] matches .error _
#guard admitOMPTeamsDirective functionTranslation [0] matches .error _
#guard ompCancellationPointDirectiveTranslationWitness matches .ok ()
#guard admitOMPCancellationPointDirective ompCancellationPointDirectiveTranslation [] matches .error _
#guard admitOMPCancellationPointDirective functionTranslation [0] matches .error _
#guard ompCancelDirectiveTranslationWitness matches .ok ()
#guard admitOMPCancelDirective ompCancelDirectiveTranslation [] matches .error _
#guard admitOMPCancelDirective functionTranslation [0] matches .error _
#guard ompScopeDirectiveTranslationWitness matches .ok ()
#guard admitOMPScopeDirective ompScopeDirectiveTranslation [] matches .error _
#guard admitOMPScopeDirective functionTranslation [0] matches .error _
#guard ompMaskedTaskLoopDirectiveTranslationWitness matches .ok ()
#guard admitOMPMaskedTaskLoopDirective ompMaskedTaskLoopDirectiveTranslation [] matches .error _
#guard admitOMPMaskedTaskLoopDirective functionTranslation [0] matches .error _
#guard ompMaskedTaskLoopSimdDirectiveTranslationWitness matches .ok ()
#guard admitOMPMaskedTaskLoopSimdDirective ompMaskedTaskLoopSimdDirectiveTranslation [] matches .error _
#guard admitOMPMaskedTaskLoopSimdDirective functionTranslation [0] matches .error _
#guard ompParallelMaskedTaskLoopDirectiveTranslationWitness matches .ok ()
#guard admitOMPParallelMaskedTaskLoopDirective ompParallelMaskedTaskLoopDirectiveTranslation [] matches .error _
#guard admitOMPParallelMaskedTaskLoopDirective functionTranslation [0] matches .error _
#guard ompParallelMaskedTaskLoopSimdDirectiveTranslationWitness matches .ok ()
#guard admitOMPParallelMaskedTaskLoopSimdDirective ompParallelMaskedTaskLoopSimdDirectiveTranslation [] matches .error _
#guard admitOMPParallelMaskedTaskLoopSimdDirective functionTranslation [0] matches .error _
#guard ompTeamsDistributeDirectiveTranslationWitness matches .ok ()
#guard admitOMPTeamsDistributeDirective ompTeamsDistributeDirectiveTranslation [] matches .error _
#guard admitOMPTeamsDistributeDirective functionTranslation [0] matches .error _
#guard ompTeamsDistributeSimdDirectiveTranslationWitness matches .ok ()
#guard admitOMPTeamsDistributeSimdDirective ompTeamsDistributeSimdDirectiveTranslation [] matches .error _
#guard admitOMPTeamsDistributeSimdDirective functionTranslation [0] matches .error _
#guard ompTeamsDistributeParallelForDirectiveTranslationWitness matches .ok ()
#guard admitOMPTeamsDistributeParallelForDirective ompTeamsDistributeParallelForDirectiveTranslation [] matches .error _
#guard admitOMPTeamsDistributeParallelForDirective functionTranslation [0] matches .error _
#guard ompTeamsDistributeParallelForSimdDirectiveTranslationWitness matches .ok ()
#guard admitOMPTeamsDistributeParallelForSimdDirective ompTeamsDistributeParallelForSimdDirectiveTranslation [] matches .error _
#guard admitOMPTeamsDistributeParallelForSimdDirective functionTranslation [0] matches .error _
#guard ompTargetDirectiveTranslationWitness matches .ok ()
#guard admitOMPTargetDirective ompTargetDirectiveTranslation [] matches .error _
#guard admitOMPTargetDirective functionTranslation [0] matches .error _
#guard ompTargetDataDirectiveTranslationWitness matches .ok ()
#guard admitOMPTargetDataDirective ompTargetDataDirectiveTranslation [] matches .error _
#guard admitOMPTargetDataDirective functionTranslation [0] matches .error _
#guard ompTargetEnterDataDirectiveTranslationWitness matches .ok ()
#guard admitOMPTargetEnterDataDirective ompTargetEnterDataDirectiveTranslation [] matches .error _
#guard admitOMPTargetEnterDataDirective functionTranslation [0] matches .error _
#guard ompTargetExitDataDirectiveTranslationWitness matches .ok ()
#guard admitOMPTargetExitDataDirective ompTargetExitDataDirectiveTranslation [] matches .error _
#guard admitOMPTargetExitDataDirective functionTranslation [0] matches .error _
#guard ompTargetParallelDirectiveTranslationWitness matches .ok ()
#guard admitOMPTargetParallelDirective ompTargetParallelDirectiveTranslation [] matches .error _
#guard admitOMPTargetParallelDirective functionTranslation [0] matches .error _
#guard ompTargetParallelForDirectiveTranslationWitness matches .ok ()
#guard admitOMPTargetParallelForDirective ompTargetParallelForDirectiveTranslation [] matches .error _
#guard admitOMPTargetParallelForDirective functionTranslation [0] matches .error _
#guard ompTargetParallelForSimdDirectiveTranslationWitness matches .ok ()
#guard admitOMPTargetParallelForSimdDirective ompTargetParallelForSimdDirectiveTranslation [] matches .error _
#guard admitOMPTargetParallelForSimdDirective functionTranslation [0] matches .error _
#guard ompTargetSimdDirectiveTranslationWitness matches .ok ()
#guard admitOMPTargetSimdDirective ompTargetSimdDirectiveTranslation [] matches .error _
#guard admitOMPTargetSimdDirective functionTranslation [0] matches .error _
#guard ompTargetUpdateDirectiveTranslationWitness matches .ok ()
#guard admitOMPTargetUpdateDirective ompTargetUpdateDirectiveTranslation [] matches .error _
#guard admitOMPTargetUpdateDirective functionTranslation [0] matches .error _
#guard ompDistributeDirectiveTranslationWitness matches .ok ()
#guard admitOMPDistributeDirective ompDistributeDirectiveTranslation [] matches .error _
#guard admitOMPDistributeDirective functionTranslation [0] matches .error _
#guard ompDistributeParallelForDirectiveTranslationWitness matches .ok ()
#guard admitOMPDistributeParallelForDirective ompDistributeParallelForDirectiveTranslation [] matches .error _
#guard admitOMPDistributeParallelForDirective functionTranslation [0] matches .error _
#guard ompDistributeParallelForSimdDirectiveTranslationWitness matches .ok ()
#guard admitOMPDistributeParallelForSimdDirective ompDistributeParallelForSimdDirectiveTranslation [] matches .error _
#guard admitOMPDistributeParallelForSimdDirective functionTranslation [0] matches .error _
#guard ompDistributeSimdDirectiveTranslationWitness matches .ok ()
#guard admitOMPDistributeSimdDirective ompDistributeSimdDirectiveTranslation [] matches .error _
#guard admitOMPDistributeSimdDirective functionTranslation [0] matches .error _
#guard ompParallelForDirectiveTranslationWitness matches .ok ()
#guard admitOMPParallelForDirective ompParallelForDirectiveTranslation [] matches .error _
#guard admitOMPParallelForDirective functionTranslation [0] matches .error _
#guard ompParallelForSimdDirectiveTranslationWitness matches .ok ()
#guard admitOMPParallelForSimdDirective ompParallelForSimdDirectiveTranslation [] matches .error _
#guard admitOMPParallelForSimdDirective functionTranslation [0] matches .error _
#guard ompParallelSectionsDirectiveTranslationWitness matches .ok ()
#guard admitOMPParallelSectionsDirective ompParallelSectionsDirectiveTranslation [] matches .error _
#guard admitOMPParallelSectionsDirective functionTranslation [0] matches .error _
#guard ompParallelMasterDirectiveTranslationWitness matches .ok ()
#guard admitOMPParallelMasterDirective ompParallelMasterDirectiveTranslation [] matches .error _
#guard admitOMPParallelMasterDirective functionTranslation [0] matches .error _
#guard ompOrderedDirectiveTranslationWitness matches .ok ()
#guard admitOMPOrderedDirective ompOrderedDirectiveTranslation [] matches .error _
#guard admitOMPOrderedDirective functionTranslation [0] matches .error _
#guard ompAtomicDirectiveTranslationWitness matches .ok ()
#guard admitOMPAtomicDirective ompAtomicDirectiveTranslation [] matches .error _
#guard admitOMPAtomicDirective functionTranslation [0] matches .error _
#guard ompFlushDirectiveTranslationWitness matches .ok ()
#guard admitOMPFlushDirective ompFlushDirectiveTranslation [] matches .error _
#guard admitOMPFlushDirective functionTranslation [0] matches .error _
#guard ompBarrierDirectiveTranslationWitness matches .ok ()
#guard admitOMPBarrierDirective ompBarrierDirectiveTranslation [] matches .error _
#guard admitOMPBarrierDirective functionTranslation [0] matches .error _
#guard ompTaskwaitDirectiveTranslationWitness matches .ok ()
#guard admitOMPTaskwaitDirective ompTaskwaitDirectiveTranslation [] matches .error _
#guard admitOMPTaskwaitDirective functionTranslation [0] matches .error _
#guard ompTaskgroupDirectiveTranslationWitness matches .ok ()
#guard admitOMPTaskgroupDirective ompTaskgroupDirectiveTranslation [] matches .error _
#guard admitOMPTaskgroupDirective functionTranslation [0] matches .error _
#guard ompMasterTaskloopDirectiveTranslationWitness matches .ok ()
#guard admitOMPMasterTaskloopDirective ompMasterTaskloopDirectiveTranslation [] matches .error _
#guard admitOMPMasterTaskloopDirective functionTranslation [0] matches .error _
#guard ompMasterTaskloopSimdDirectiveTranslationWitness matches .ok ()
#guard admitOMPMasterTaskloopSimdDirective ompMasterTaskloopSimdDirectiveTranslation [] matches .error _
#guard admitOMPMasterTaskloopSimdDirective functionTranslation [0] matches .error _
#guard ompParallelMasterTaskloopDirectiveTranslationWitness matches .ok ()
#guard admitOMPParallelMasterTaskloopDirective ompParallelMasterTaskloopDirectiveTranslation [] matches .error _
#guard admitOMPParallelMasterTaskloopDirective functionTranslation [0] matches .error _
#guard ompParallelMasterTaskloopSimdDirectiveTranslationWitness matches .ok ()
#guard admitOMPParallelMasterTaskloopSimdDirective ompParallelMasterTaskloopSimdDirectiveTranslation [] matches .error _
#guard admitOMPParallelMasterTaskloopSimdDirective functionTranslation [0] matches .error _
#guard ompTaskyieldDirectiveTranslationWitness matches .ok ()
#guard admitOMPTaskyieldDirective ompTaskyieldDirectiveTranslation [] matches .error _
#guard admitOMPTaskyieldDirective functionTranslation [0] matches .error _
#guard conditionalOperatorTranslationWitness matches .ok ()
#guard admitConditionalOperatorExpression conditionalOperatorTranslation [] matches .error _
#guard admitConditionalOperatorExpression functionTranslation [0] matches .error _
#guard callTranslationWitness matches .ok ()
#guard admitCallExpression callTranslation [] matches .error _
#guard admitCallExpression functionTranslation [0] matches .error _
#guard compoundAssignmentTranslationWitness matches .ok ()
#guard admitCompoundAssignmentOperator compoundAssignmentTranslation [] matches .error _
#guard admitCompoundAssignmentOperator functionTranslation [0] matches .error _
#guard lambdaTranslationWitness matches .ok ()
#guard admitLambdaExpression lambdaTranslation [] matches .error _
#guard admitLambdaExpression functionTranslation [0] matches .error _
#guard arraySubscriptTranslationWitness matches .ok ()
#guard admitArraySubscriptExpression arraySubscriptTranslation [] matches .error _
#guard admitArraySubscriptExpression functionTranslation [0] matches .error _
#guard memberExpressionTranslationWitness matches .ok ()
#guard admitMemberExpression memberExpressionTranslation [] matches .error _
#guard admitMemberExpression functionTranslation [0] matches .error _
#guard cxxMemberCallExpressionTranslationWitness matches .ok ()
#guard admitCXXMemberCallExpression cxxMemberCallExpressionTranslation [] matches .error _
#guard admitCXXMemberCallExpression functionTranslation [0] matches .error _
#guard cxxOperatorCallExpressionTranslationWitness matches .ok ()
#guard admitCXXOperatorCallExpression cxxOperatorCallExpressionTranslation [] matches .error _
#guard admitCXXOperatorCallExpression functionTranslation [0] matches .error _
#guard compoundStatementTranslationWitness matches .ok ()
#guard admitCompoundStatement compoundStatementTranslation [] matches .error _
#guard admitCompoundStatement functionTranslation [0] matches .error _
#guard returnStatementTranslationWitness matches .ok ()
#guard admitReturnStatement returnStatementTranslation [] matches .error _
#guard admitReturnStatement functionTranslation [0] matches .error _
#guard ifStatementTranslationWitness matches .ok ()
#guard admitIfStatement ifStatementTranslation [] matches .error _
#guard admitIfStatement functionTranslation [0] matches .error _
#guard whileStatementTranslationWitness matches .ok ()
#guard admitWhileStatement whileStatementTranslation [] matches .error _
#guard admitWhileStatement functionTranslation [0] matches .error _
#guard doStatementTranslationWitness matches .ok ()
#guard admitDoStatement doStatementTranslation [] matches .error _
#guard admitDoStatement functionTranslation [0] matches .error _
#guard forStatementTranslationWitness matches .ok ()
#guard admitForStatement forStatementTranslation [] matches .error _
#guard admitForStatement functionTranslation [0] matches .error _
#guard rangeForStatementTranslationWitness matches .ok ()
#guard admitRangeForStatement rangeForStatementTranslation [] matches .error _
#guard admitRangeForStatement functionTranslation [0] matches .error _
#guard switchStatementTranslationWitness matches .ok ()
#guard admitSwitchStatement switchStatementTranslation [] matches .error _
#guard admitSwitchStatement functionTranslation [0] matches .error _
#guard caseStatementTranslationWitness matches .ok ()
#guard admitCaseStatement caseStatementTranslation [] matches .error _
#guard admitCaseStatement functionTranslation [0] matches .error _
#guard defaultStatementTranslationWitness matches .ok ()
#guard admitDefaultStatement defaultStatementTranslation [] matches .error _
#guard admitDefaultStatement functionTranslation [0] matches .error _
#guard declarationStatementTranslationWitness matches .ok ()
#guard admitDeclarationStatement declarationStatementTranslation [] matches .error _
#guard admitDeclarationStatement functionTranslation [0] matches .error _
#guard breakStatementTranslationWitness matches .ok ()
#guard admitBreakStatement breakStatementTranslation [] matches .error _
#guard admitBreakStatement functionTranslation [0] matches .error _
#guard continueStatementTranslationWitness matches .ok ()
#guard admitContinueStatement continueStatementTranslation [] matches .error _
#guard admitContinueStatement functionTranslation [0] matches .error _
#guard nullStatementTranslationWitness matches .ok ()
#guard admitNullStatement nullStatementTranslation [] matches .error _
#guard admitNullStatement functionTranslation [0] matches .error _
#guard gotoStatementTranslationWitness matches .ok ()
#guard admitGotoStatement gotoStatementTranslation [] matches .error _
#guard admitGotoStatement functionTranslation [0] matches .error _
#guard labelStatementTranslationWitness matches .ok ()
#guard admitLabelStatement labelStatementTranslation [] matches .error _
#guard admitLabelStatement functionTranslation [0] matches .error _
#guard labelDeclarationTranslationWitness matches .ok ()
#guard admitLabelDeclaration labelDeclarationTranslation [] matches .error _
#guard admitLabelDeclaration functionTranslation [0] matches .error _
#guard cxxTryStatementTranslationWitness matches .ok ()
#guard admitCXXTryStatement cxxTryStatementTranslation [] matches .error _
#guard admitCXXTryStatement functionTranslation [0] matches .error _
#guard cxxCatchStatementTranslationWitness matches .ok ()
#guard admitCXXCatchStatement cxxCatchStatementTranslation [] matches .error _
#guard admitCXXCatchStatement functionTranslation [0] matches .error _
#guard cxxThrowExpressionTranslationWitness matches .ok ()
#guard admitCXXThrowExpression cxxThrowExpressionTranslation [] matches .error _
#guard admitCXXThrowExpression functionTranslation [0] matches .error _
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
