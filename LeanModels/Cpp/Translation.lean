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

def admitRecordDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXRecordDecl" "record"

def admitBaseSpecifier (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXBaseSpecifier" "base-specifier"

def admitFieldDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "FieldDecl" "field"

def admitMethodDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXMethodDecl" "method"

def admitEnumConstantDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "EnumConstantDecl" "enum-constant"

def admitAccessSpecification (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "AccessSpecDecl" "access-specification"

def admitConstructorDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXConstructorDecl" "constructor"

def admitDestructorDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXDestructorDecl" "destructor"

def admitConversionDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXConversionDecl" "conversion"

def admitFriendDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "FriendDecl" "friend"

def admitTemplateTypeParameter (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "TemplateTypeParmDecl" "template-type-parameter"

def admitNonTypeTemplateParameter (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "NonTypeTemplateParmDecl" "non-type-template-parameter"

def admitTemplateTemplateParameter (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "TemplateTemplateParmDecl" "template-template-parameter"

def admitClassTemplateDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ClassTemplateDecl" "class-template"

def admitFunctionTemplateDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "FunctionTemplateDecl" "function-template"

def admitVariableTemplateDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "VarTemplateDecl" "variable-template"

def admitTypeAliasTemplateDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "TypeAliasTemplateDecl" "type-alias-template"

def admitClassTemplateSpecializationDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ClassTemplateSpecializationDecl" "class-template-specialization"

def admitVariableTemplateSpecializationDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "VarTemplateSpecializationDecl" "variable-template-specialization"

def admitClassTemplatePartialSpecializationDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ClassTemplatePartialSpecializationDecl" "class-template-partial-specialization"

def admitVariableTemplatePartialSpecializationDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "VarTemplatePartialSpecializationDecl" "variable-template-partial-specialization"

def admitConceptDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ConceptDecl" "concept"

def admitDeductionGuideDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXDeductionGuideDecl" "deduction-guide"

def admitUsingShadowDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "UsingShadowDecl" "using-shadow"

def admitConstructorUsingShadowDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ConstructorUsingShadowDecl" "constructor-using-shadow"

def admitUsingPackDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "UsingPackDecl" "using-pack"

def admitUnresolvedUsingTypenameDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "UnresolvedUsingTypenameDecl" "unresolved-using-typename"

def admitUnresolvedUsingValueDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "UnresolvedUsingValueDecl" "unresolved-using-value"

def admitBindingDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "BindingDecl" "binding"

def admitDecompositionDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "DecompositionDecl" "decomposition"

def admitIndirectFieldDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "IndirectFieldDecl" "indirect-field"

def admitClassScopeFunctionSpecializationDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ClassScopeFunctionSpecializationDecl" "class-scope-function-specialization"

def admitFriendTemplateDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "FriendTemplateDecl" "friend-template"

def admitTemplateParamObjectDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "TemplateParamObjectDecl" "template-param-object"

def admitImplicitConceptSpecializationDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ImplicitConceptSpecializationDecl" "implicit-concept-specialization"

def admitRequiresExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "RequiresExpr" "requires-expression"

def admitTypeRequirement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "TypeRequirement" "type-requirement"

def admitSimpleRequirement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "SimpleRequirement" "simple-requirement"

def admitCompoundRequirement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CompoundRequirement" "compound-requirement"

def admitNestedRequirement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "NestedRequirement" "nested-requirement"

def admitUsingEnumDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "UsingEnumDecl" "using-enum"

def admitLifetimeExtendedTemporaryDeclaration (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "LifetimeExtendedTemporaryDecl" "lifetime-extended-temporary"

def admitMaterializeTemporaryExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "MaterializeTemporaryExpr" "materialize-temporary"

def admitCXXBindTemporaryExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXBindTemporaryExpr" "bind-temporary"

def admitExpressionWithCleanups (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ExprWithCleanups" "expression-with-cleanups"

def admitCXXTemporaryObjectExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXTemporaryObjectExpr" "temporary-object"

def admitCXXConstructExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXConstructExpr" "construct-expression"

def admitCXXNewExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXNewExpr" "new-expression"

def admitCXXDeleteExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXDeleteExpr" "delete-expression"

def admitCXXDefaultInitExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXDefaultInitExpr" "default-init-expression"

def admitCXXScalarValueInitExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXScalarValueInitExpr" "scalar-value-init-expression"

def admitInitializerListExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "InitListExpr" "initializer-list-expression"

def admitCXXParenListInitExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXParenListInitExpr" "paren-list-init-expression"

def admitImplicitValueInitExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ImplicitValueInitExpr" "implicit-value-init-expression"

def admitImplicitCastExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ImplicitCastExpr" "implicit-cast-expression"

def admitParenthesizedExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ParenExpr" "parenthesized-expression"

def admitConstantExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ConstantExpr" "constant-expression"

def admitCXXStaticCastExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXStaticCastExpr" "static-cast-expression"

def admitCXXConstCastExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXConstCastExpr" "const-cast-expression"

def admitCXXReinterpretCastExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXReinterpretCastExpr" "reinterpret-cast-expression"

def admitCXXDynamicCastExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXDynamicCastExpr" "dynamic-cast-expression"

def admitCXXBoolLiteralExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXBoolLiteralExpr" "bool-literal-expression"

def admitCXXNullPtrLiteralExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXNullPtrLiteralExpr" "nullptr-literal-expression"

def admitCharacterLiteralExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CharacterLiteral" "character-literal-expression"

def admitFloatingLiteralExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "FloatingLiteral" "floating-literal-expression"

def admitStringLiteralExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "StringLiteral" "string-literal-expression"

def admitIntegerLiteralExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "IntegerLiteral" "integer-literal-expression"

def admitDeclarationReferenceExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "DeclRefExpr" "declaration-reference-expression"

def admitCXXThisExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXThisExpr" "this-expression"

def admitUnaryOperatorExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "UnaryOperator" "unary-operator-expression"

def admitBinaryOperatorExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "BinaryOperator" "binary-operator-expression"

def admitConditionalOperatorExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ConditionalOperator" "conditional-operator-expression"

def admitCallExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CallExpr" "call-expression"

def admitCompoundAssignmentOperator (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CompoundAssignOperator" "compound-assignment-operator"

def admitLambdaExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "LambdaExpr" "lambda-expression"

def admitArraySubscriptExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ArraySubscriptExpr" "array-subscript-expression"

def admitMemberExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "MemberExpr" "member-expression"

def admitCompoundStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CompoundStmt" "compound-statement"

def admitReturnStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ReturnStmt" "return-statement"

def admitIfStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "IfStmt" "if-statement"

def admitWhileStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "WhileStmt" "while-statement"

def admitDoStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "DoStmt" "do-statement"

def admitForStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ForStmt" "for-statement"

def admitRangeForStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXForRangeStmt" "range-for-statement"

def admitSwitchStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "SwitchStmt" "switch-statement"

def admitCaseStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CaseStmt" "case-statement"

def admitDefaultStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "DefaultStmt" "default-statement"

def admitDeclarationStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "DeclStmt" "declaration-statement"

def admitBreakStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "BreakStmt" "break-statement"

def admitContinueStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "ContinueStmt" "continue-statement"

def admitNullStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "NullStmt" "null-statement"

def admitGotoStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "GotoStmt" "goto-statement"

def admitLabelStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "LabelStmt" "label-statement"

def admitCXXTryStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXTryStmt" "try-statement"

def admitCXXCatchStatement (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXCatchStmt" "catch-statement"

def admitCXXThrowExpression (artifact : Artifact) (path : List Nat) :
    Except String Unit := admitDeclarationKind artifact path "CXXThrowExpr" "throw-expression"

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
