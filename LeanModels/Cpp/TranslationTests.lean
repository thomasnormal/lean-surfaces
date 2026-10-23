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
