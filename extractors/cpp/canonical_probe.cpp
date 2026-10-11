#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"
#include "clang/Basic/Module.h"
#include "clang/Basic/Version.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"

#include <optional>
#include <unordered_set>
#include <vector>

#if CLANG_VERSION_MAJOR != 21 || CLANG_VERSION_MINOR != 1 || CLANG_VERSION_PATCHLEVEL != 8
#error "canonical probe supports only Clang 21.1.8 headers"
#endif

#if LLVM_VERSION_MAJOR != 21 || LLVM_VERSION_MINOR != 1 || LLVM_VERSION_PATCH != 8
#error "canonical probe supports only LLVM 21.1.8 headers"
#endif

namespace {

std::string pointerId(const void *pointer) {
  return "0x" + llvm::utohexstr(reinterpret_cast<uintptr_t>(pointer), true);
}

llvm::json::Value declarationId(const clang::Decl *declaration) {
  if (!declaration)
    return nullptr;
  return pointerId(declaration);
}

llvm::json::Value contextId(const clang::DeclContext *context) {
  if (!context)
    return nullptr;
  return declarationId(clang::Decl::castFromDeclContext(context));
}

std::string linkageName(clang::Linkage linkage) {
  switch (linkage) {
  case clang::Linkage::Invalid: return "Invalid";
  case clang::Linkage::None: return "None";
  case clang::Linkage::Internal: return "Internal";
  case clang::Linkage::UniqueExternal: return "UniqueExternal";
  case clang::Linkage::VisibleNone: return "VisibleNone";
  case clang::Linkage::Module: return "Module";
  case clang::Linkage::External: return "External";
  }
  return "unrepresented";
}

std::string languageLinkageName(clang::LanguageLinkage linkage) {
  switch (linkage) {
  case clang::CLanguageLinkage: return "C";
  case clang::CXXLanguageLinkage: return "C++";
  case clang::NoLanguageLinkage: return "None";
  }
  return "unrepresented";
}

void functionShapeEvidence(const clang::FunctionDecl *function,
                           llvm::json::Object &record) {
  record["function_has_skipped_body"] = function->hasSkippedBody();
  record["function_has_skipped_body_api"] = "FunctionDecl.hasSkippedBody";
  record["function_will_have_body"] = function->willHaveBody();
  record["function_will_have_body_api"] = "FunctionDecl.willHaveBody";
  record["function_has_defining_attr"] = function->hasDefiningAttr();
  record["function_has_defining_attr_api"] = "FunctionDecl.hasDefiningAttr";
  record["function_late_template_parsed"] = function->isLateTemplateParsed();
  record["function_late_template_parsed_api"] = "FunctionDecl.isLateTemplateParsed";
  record["function_explicitly_defaulted"] = function->isExplicitlyDefaulted();
  record["function_explicitly_defaulted_api"] = "FunctionDecl.isExplicitlyDefaulted";
  record["function_attribute_count"] =
      static_cast<int64_t>(function->hasAttrs() ? function->getAttrs().size() : 0);
  record["function_attribute_count_api"] = "Decl.hasAttrs/Decl.getAttrs.size";
  record["own_body_kind"] = nullptr;
  record["own_body_owner"] = nullptr;
  record["own_body_api"] = "FunctionDecl.getBody";
  if (function->doesThisDeclarationHaveABody() && !function->isLateTemplateParsed()) {
    const clang::FunctionDecl *owner = nullptr;
    const clang::Stmt *body = function->getBody(owner);
    record["own_body_owner"] = declarationId(owner);
    if (body)
      record["own_body_kind"] = body->getStmtClassName();
  }
}

void definitionEvidence(const clang::Decl *declaration,
                        llvm::json::Object &record) {
  record["definition"] = nullptr;
  record["definition_api"] = "not-queried";
  if (const auto *function = llvm::dyn_cast<clang::FunctionDecl>(declaration)) {
    record["definition"] = function->isThisDeclarationADefinition();
    record["definition_api"] = "FunctionDecl.isThisDeclarationADefinition";
    record["body_present"] = function->doesThisDeclarationHaveABody();
    record["defaulted"] = function->isDefaulted();
    record["deleted_as_written"] = function->isDeletedAsWritten();
    functionShapeEvidence(function, record);
    record["language_linkage"] = languageLinkageName(function->getLanguageLinkage());
  } else if (const auto *variable = llvm::dyn_cast<clang::VarDecl>(declaration)) {
    record["definition_api"] = "VarDecl.isThisDeclarationADefinition";
    record["variable_definition_kind"] =
        static_cast<int>(variable->isThisDeclarationADefinition());
    record["language_linkage"] = languageLinkageName(variable->getLanguageLinkage());
  } else if (const auto *tag = llvm::dyn_cast<clang::TagDecl>(declaration)) {
    record["definition"] = tag->isThisDeclarationADefinition();
    record["definition_api"] = "TagDecl.isThisDeclarationADefinition";
  }
}

void templateEvidence(const clang::Decl *declaration, llvm::json::Object &record) {
  if (const auto *function = llvm::dyn_cast<clang::FunctionDecl>(declaration)) {
    record["function_templated_kind"] = static_cast<int>(function->getTemplatedKind());
    record["function_templated_kind_api"] = "FunctionDecl.getTemplatedKind";
    record["template_specialization_kind"] =
        static_cast<int>(function->getTemplateSpecializationKind());
    record["template_specialization_kind_api"] = "FunctionDecl.getTemplateSpecializationKind";
  } else if (const auto *variable = llvm::dyn_cast<clang::VarDecl>(declaration)) {
    record["described_template"] = declarationId(variable->getDescribedVarTemplate());
    record["described_template_api"] = "VarDecl.getDescribedVarTemplate";
    record["template_specialization_kind"] =
        static_cast<int>(variable->getTemplateSpecializationKind());
    record["template_specialization_kind_api"] = "VarDecl.getTemplateSpecializationKind";
  } else if (const auto *classDeclaration = llvm::dyn_cast<clang::CXXRecordDecl>(declaration)) {
    record["described_template"] = declarationId(classDeclaration->getDescribedClassTemplate());
    record["described_template_api"] = "CXXRecordDecl.getDescribedClassTemplate";
    record["template_specialization_kind"] =
        static_cast<int>(classDeclaration->getTemplateSpecializationKind());
    record["template_specialization_kind_api"] = "CXXRecordDecl.getTemplateSpecializationKind";
  } else if (const auto *enumeration = llvm::dyn_cast<clang::EnumDecl>(declaration)) {
    record["template_specialization_kind"] =
        static_cast<int>(enumeration->getTemplateSpecializationKind());
    record["template_specialization_kind_api"] = "EnumDecl.getTemplateSpecializationKind";
  }
}

void classEvidence(const clang::Decl *declaration, llvm::json::Object &record) {
  const auto *classDeclaration = llvm::dyn_cast<clang::CXXRecordDecl>(declaration);
  if (!classDeclaration)
    return;
  record["injected_class_name"] = classDeclaration->isInjectedClassName();
  record["represented_class"] = nullptr;
  if (classDeclaration->isInjectedClassName() && classDeclaration->getTypeForDecl())
    record["represented_class"] =
        declarationId(classDeclaration->getTypeForDecl()->getAsCXXRecordDecl());
}

std::optional<std::string> builtinTypeName(const clang::BuiltinType *builtin) {
  switch (builtin->getKind()) {
  case clang::BuiltinType::Bool: return "bool";
  case clang::BuiltinType::Char_S:
  case clang::BuiltinType::Char_U: return "char";
  case clang::BuiltinType::SChar: return "signed char";
  case clang::BuiltinType::UChar: return "unsigned char";
  case clang::BuiltinType::Short: return "short";
  case clang::BuiltinType::UShort: return "unsigned short";
  case clang::BuiltinType::Int: return "int";
  case clang::BuiltinType::UInt: return "unsigned int";
  case clang::BuiltinType::Long: return "long";
  case clang::BuiltinType::ULong: return "unsigned long";
  case clang::BuiltinType::LongLong: return "long long";
  case clang::BuiltinType::ULongLong: return "unsigned long long";
  default: return std::nullopt;
  }
}

std::optional<llvm::json::Value> structuredType(
    clang::QualType qualified, const clang::ASTContext &context, unsigned depth);

std::optional<llvm::json::Value>
structuredUnqualifiedType(clang::QualType unqualified,
                          const clang::ASTContext &context, unsigned depth) {
  const clang::Type *type = unqualified.getTypePtrOrNull();
  if (!type)
    return std::nullopt;
  if (const auto *builtin = llvm::dyn_cast<clang::BuiltinType>(type)) {
    const auto name = builtinTypeName(builtin);
    if (!name)
      return std::nullopt;
    llvm::json::Object result;
    result["kind"] = "builtin";
    result["name"] = *name;
    return llvm::json::Value(std::move(result));
  }
  if (const auto *pointer = llvm::dyn_cast<clang::PointerType>(type)) {
    auto pointee = structuredType(pointer->getPointeeType(), context, depth + 1);
    if (!pointee)
      return std::nullopt;
    llvm::json::Object result;
    result["kind"] = "pointer";
    result["pointee"] = std::move(*pointee);
    return llvm::json::Value(std::move(result));
  }
  if (const auto *reference = llvm::dyn_cast<clang::LValueReferenceType>(type)) {
    auto referent = structuredType(reference->getPointeeType(), context, depth + 1);
    if (!referent)
      return std::nullopt;
    llvm::json::Object result;
    result["kind"] = "lvalue-reference";
    result["referent"] = std::move(*referent);
    return llvm::json::Value(std::move(result));
  }
  if (const auto *reference = llvm::dyn_cast<clang::RValueReferenceType>(type)) {
    auto referent = structuredType(reference->getPointeeType(), context, depth + 1);
    if (!referent)
      return std::nullopt;
    llvm::json::Object result;
    result["kind"] = "rvalue-reference";
    result["referent"] = std::move(*referent);
    return llvm::json::Value(std::move(result));
  }
  if (const auto *function = llvm::dyn_cast<clang::FunctionProtoType>(type)) {
    if (function->hasExceptionSpec() || !function->getMethodQuals().empty() ||
        function->getRefQualifier() != clang::RQ_None ||
        function->getExtInfo() != clang::FunctionType::ExtInfo() ||
        function->hasExtParameterInfos() || function->hasCFIUncheckedCallee() ||
        function->getAArch64SMEAttributes() != 0 ||
        function->getNumFunctionEffects() != 0)
      return std::nullopt;
    auto resultType = structuredType(function->getReturnType(), context, depth + 1);
    if (!resultType)
      return std::nullopt;
    llvm::json::Array parameters;
    for (const clang::QualType parameter : function->param_types()) {
      auto parameterType = structuredType(parameter, context, depth + 1);
      if (!parameterType)
        return std::nullopt;
      parameters.push_back(std::move(*parameterType));
    }
    llvm::json::Object result;
    result["kind"] = "function";
    result["result"] = std::move(*resultType);
    result["parameters"] = std::move(parameters);
    result["variadic"] = function->isVariadic();
    return llvm::json::Value(std::move(result));
  }
  if (const auto *record = llvm::dyn_cast<clang::RecordType>(type)) {
    const clang::RecordDecl *declaration = record->getDecl();
    if (!declaration)
      return std::nullopt;
    llvm::json::Object result;
    result["kind"] = "record";
    result["declaration"] = declarationId(declaration->getCanonicalDecl());
    return llvm::json::Value(std::move(result));
  }
  if (const auto *enumeration = llvm::dyn_cast<clang::EnumType>(type)) {
    const clang::EnumDecl *declaration = enumeration->getDecl();
    if (!declaration)
      return std::nullopt;
    llvm::json::Object result;
    result["kind"] = "enumeration";
    result["declaration"] = declarationId(declaration->getCanonicalDecl());
    return llvm::json::Value(std::move(result));
  }
  return std::nullopt;
}

std::optional<llvm::json::Value> structuredType(
    clang::QualType qualified, const clang::ASTContext &context, unsigned depth) {
  if (qualified.isNull() || depth >= 128)
    return std::nullopt;
  const clang::QualType desugared = qualified.getDesugaredType(context);
  const clang::Qualifiers qualifiers = desugared.getLocalQualifiers();
  if (qualifiers.hasRestrict() || qualifiers.hasNonFastQualifiers())
    return std::nullopt;
  const bool isConst = qualifiers.hasConst();
  const bool isVolatile = qualifiers.hasVolatile();
  auto body = structuredUnqualifiedType(desugared.getLocalUnqualifiedType(), context, depth);
  if (!body)
    return std::nullopt;
  if (!isConst && !isVolatile)
    return body;
  llvm::json::Object result;
  result["kind"] = "qualified";
  result["const"] = isConst;
  result["volatile"] = isVolatile;
  result["base"] = std::move(*body);
  return llvm::json::Value(std::move(result));
}

std::optional<clang::QualType> declarationType(const clang::Decl *declaration) {
  if (const auto *function = llvm::dyn_cast<clang::FunctionDecl>(declaration))
    return function->getType();
  if (const auto *value = llvm::dyn_cast<clang::ValueDecl>(declaration))
    return value->getType();
  return std::nullopt;
}

bool structuredReferencesWitnessed(
    const llvm::json::Value &value,
    const std::unordered_set<std::string> &declarationIds) {
  if (const auto *object = value.getAsObject()) {
    if (const auto kind = object->getString("kind"); kind &&
        (*kind == "record" || *kind == "enumeration")) {
      const auto declaration = object->getString("declaration");
      if (!declaration || !declarationIds.count(declaration->str()))
        return false;
    }
    for (const auto &entry : *object)
      if (!structuredReferencesWitnessed(entry.second, declarationIds))
        return false;
    return true;
  }
  if (const auto *array = value.getAsArray()) {
    for (const auto &entry : *array)
      if (!structuredReferencesWitnessed(entry, declarationIds))
        return false;
  }
  return true;
}

class DeclarationVisitor : public clang::RecursiveASTVisitor<DeclarationVisitor> {
public:
  llvm::json::Array records;
  llvm::json::Array typeEvidence;
  llvm::json::Array typeRefusals;
  llvm::json::Array expressionEvidence;
  llvm::json::Array expressionRefusals;
  std::vector<const clang::Decl *> typedDeclarations;
  std::vector<const clang::BinaryOperator *> binaryExpressions;
  std::unordered_set<std::string> declarationIds;
  const clang::ASTContext *astContext = nullptr;

  bool shouldVisitImplicitCode() const { return true; }
  bool shouldVisitTemplateInstantiations() const { return true; }

  bool VisitDecl(clang::Decl *declaration) {
    declarationIds.insert(pointerId(declaration));
    llvm::json::Object record{
        {"id", pointerId(declaration)},
        {"kind", std::string(declaration->getDeclKindName()) + "Decl"},
        {"canonical", declarationId(declaration->getCanonicalDecl())},
        {"previous", declarationId(declaration->getPreviousDecl())},
        {"semantic_context", contextId(declaration->getDeclContext())},
        {"lexical_context", contextId(declaration->getLexicalDeclContext())},
        {"implicit", declaration->isImplicit()},
        {"dependent_context", declaration->getDeclContext() &&
             declaration->getDeclContext()->isDependentContext()},
        {"owning_module", nullptr}};
    if (const auto *module = declaration->getOwningModule())
      record["owning_module"] = module->getFullModuleName();
    if (const auto *named = llvm::dyn_cast<clang::NamedDecl>(declaration)) {
      record["name"] = named->getNameAsString();
      record["linkage_internal"] = linkageName(named->getLinkageInternal());
      record["linkage_formal"] = linkageName(named->getFormalLinkage());
    }
    if (const auto *nameSpace = llvm::dyn_cast<clang::NamespaceDecl>(declaration)) {
      record["original_namespace"] = declarationId(nameSpace->getCanonicalDecl());
      record["inline_namespace"] = nameSpace->isInline();
      record["anonymous_namespace"] = nameSpace->isAnonymousNamespace();
    }
    definitionEvidence(declaration, record);
    templateEvidence(declaration, record);
    classEvidence(declaration, record);
    records.push_back(std::move(record));
    if (declarationType(declaration))
      typedDeclarations.push_back(declaration);
    return true;
  }

  bool VisitBinaryOperator(clang::BinaryOperator *expression) {
    binaryExpressions.push_back(expression);
    return true;
  }

  void emitBinaryExpression(const clang::BinaryOperator *expression) {
    llvm::json::Object row{
        {"expression_api", "Clang::BinaryOperator typed operand projection v1"},
        {"occurrence", pointerId(expression)},
        {"kind", "BinaryOperator"},
        {"operator", expression->getOpcodeStr().str()}};
    auto result = structuredType(expression->getType(), *astContext, 0);
    llvm::json::Array operands;
    bool supported = result.has_value();
    for (const clang::Expr *operand : {expression->getLHS(), expression->getRHS()}) {
      llvm::json::Object operandRow{
          {"occurrence", pointerId(operand)},
          {"kind", operand->getStmtClassName()}};
      auto operandType = structuredType(operand->getType(), *astContext, 0);
      if (operandType && structuredReferencesWitnessed(*operandType, declarationIds))
        operandRow["type"] = std::move(*operandType);
      else
        supported = false;
      operands.push_back(std::move(operandRow));
    }
    if (!result || !supported || !structuredReferencesWitnessed(*result, declarationIds)) {
      row["reason"] = "unrepresented result or operand type";
      expressionRefusals.push_back(std::move(row));
      return;
    }
    row["result"] = std::move(*result);
    row["operands"] = std::move(operands);
    expressionEvidence.push_back(std::move(row));
  }

  void buildTypeEvidence(const clang::ASTContext &context) {
    for (const clang::Decl *declaration : typedDeclarations) {
      const auto type = declarationType(declaration);
      if (!type)
        continue;
      auto structured = structuredType(*type, context, 0);
      llvm::json::Object row;
      row["type_api"] = "Clang::QualType structured type projection v1";
      row["occurrence"] = pointerId(declaration);
      row["canonical"] = declarationId(declaration->getCanonicalDecl());
      if (!structured || !structuredReferencesWitnessed(*structured, declarationIds)) {
        row["reason"] = structured ? "unwitnessed record or enumeration declaration"
                                   : "unrepresented type family, qualifiers, function properties or depth";
        typeRefusals.push_back(std::move(row));
        continue;
      }
      row["type"] = std::move(*structured);
      typeEvidence.push_back(std::move(row));
    }
  }

  void buildExpressionEvidence() {
    for (const clang::BinaryOperator *expression : binaryExpressions)
      emitBinaryExpression(expression);
  }
};

class ProbeConsumer : public clang::ASTConsumer {
  clang::CompilerInstance &compiler;

public:
  explicit ProbeConsumer(clang::CompilerInstance &instance) : compiler(instance) {}

  void HandleTranslationUnit(clang::ASTContext &context) override {
    if (compiler.getDiagnostics().hasErrorOccurred())
      return;
    DeclarationVisitor visitor;
    visitor.astContext = &context;
    if (!visitor.TraverseDecl(context.getTranslationUnitDecl())) {
      unsigned diagnostic = compiler.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Error, "canonical probe traversal failed");
      compiler.getDiagnostics().Report(diagnostic);
      return;
    }
    visitor.buildTypeEvidence(context);
    visitor.buildExpressionEvidence();
    llvm::json::Object metadata{
        {"schema_version", "cpp-canonical-probe-0.3"},
        {"compiled_frontend", CLANG_VERSION_STRING},
        {"runtime_frontend", clang::getClangFullVersion()},
        {"llvm_headers", LLVM_VERSION_STRING},
        {"type_evidence_api", "Clang::QualType structured type projection v1"},
        {"type_evidence", std::move(visitor.typeEvidence)},
        {"type_refusals", std::move(visitor.typeRefusals)},
        {"expression_evidence_api", "Clang::BinaryOperator typed operand projection v1"},
        {"expression_evidence", std::move(visitor.expressionEvidence)},
        {"expression_refusals", std::move(visitor.expressionRefusals)},
        {"declarations", std::move(visitor.records)}};
    llvm::outs() << "{\"metadata\":" << llvm::formatv("{0}", llvm::json::Value(std::move(metadata)))
                 << ",\"ast\":";
    context.getTranslationUnitDecl()->dump(llvm::outs(), false, clang::ADOF_JSON);
    llvm::outs() << "}\n";
  }
};

class ProbeAction : public clang::PluginASTAction {
public:
  std::unique_ptr<clang::ASTConsumer>
  CreateASTConsumer(clang::CompilerInstance &compiler, llvm::StringRef) override {
    return std::make_unique<ProbeConsumer>(compiler);
  }

  bool ParseArgs(const clang::CompilerInstance &compiler,
                 const std::vector<std::string> &arguments) override {
    if (!arguments.empty()) {
      unsigned diagnostic = compiler.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Error, "canonical probe accepts no plugin arguments");
      compiler.getDiagnostics().Report(diagnostic);
      return false;
    }
    const std::string expected = "clang version " CLANG_VERSION_STRING;
    const std::string runtime = clang::getClangFullVersion();
    if (runtime != expected && !llvm::StringRef(runtime).starts_with(expected + " ")) {
      unsigned diagnostic = compiler.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Error, "canonical probe header/runtime version mismatch");
      compiler.getDiagnostics().Report(diagnostic);
      return false;
    }
    return true;
  }

  ActionType getActionType() override { return ReplaceAction; }
};

clang::FrontendPluginRegistry::Add<ProbeAction>
    registration("leancpp-canonical-probe", "same-process C++ declaration metadata probe");

}
